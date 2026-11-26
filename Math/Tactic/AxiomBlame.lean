module

/-
  AxiomProvenance.lean — `#axiom_paths`: like `#print axioms`, but also shows
  HOW each axiom is reached (a dependency chain with file:line), and works under
  the module system. Built on the same design as core's `exportedAxiomsExt`
  (Lean.Util.CollectAxioms, v4.35.0).

  DESIGN
  ------
  * At export time (`exportEntriesFnEx`) we look at the module through
    `env.setExporting false` (the private view, where every body is visible) and
    compute, for every constant that is visible in the exported view, one row per
    axiom it depends on:   (ax, next, dist)
        next = first constant on a shortest dependency path towards `ax`
        dist = length of that path
    Entries are stored in the .olean, sorted by name, as `.uniform` entries.
  * Importers keep each module's entries (`importedModuleEntries`) and look up a
    constant by module index + binary search, exactly as core does.
  * `#axiom_paths c` walks `next` pointers entry to entry, hopping across
    modules, so no foreign body is ever inspected. Constants of the current
    module, and constants from modules built without this extension, are solved
    live in the private view.
  * Solver = label-correcting worklist relaxation, not a DFS with an in-progress
    sentinel, so inductive ↔ constructor cycles cannot cause under-reporting
    (cf. leanprover/lean4#15226).
  * A shortest path may pass through a private/non-exported constant of another
    module, which has no entry. At export time such intermediates are elided:
    `next` is the first *visible* constant on the path (so across-module chains
    skip private helpers; chains inside the current module show everything).

  USAGE
  -----
    import AxiomProvenance      -- import it in every module you build
    #axiom_paths Nat.add_comm
    #axiom_paths foo bar

  STATUS: NOT COMPILED (no Lean toolchain here). Lines marked `-- API?` are the
  likeliest to need small adjustments.
-/
public import Lean

meta section

open Lean Elab Command

namespace AxiomProv

/-- One row of an entry: how to reach `ax` from the owning constant. -/
structure Hop where
  ax   : Name
  next : Name
  dist : Nat
  deriving Inhabited

structure Entry where
  name : Name
  hops : Array Hop
  deriving Inhabited

/-- Extension state: the entries of every imported module, by module index. -/
structure ExtState where
  importedModuleEntries : Array (Array Entry) := #[]
  deriving Inhabited

/-- Same lookup scheme as core's `ExportedAxiomsState.find?`. -/
def ExtState.find? (s : ExtState) (env : Environment) (c : Name) : Option (Array Hop) := do
  let idx ← env.getModuleIdxFor? c
  let es ← s.importedModuleEntries[idx.toNat]?
  let e ← es.binSearch ⟨c, #[]⟩ (fun a b => Name.quickLt a.name b.name)
  return e.hops

/-- Constants a declaration refers to directly. -/
def directDeps (ci : ConstantInfo) : Array Name :=
  match ci with
  | .inductInfo v => ci.getUsedConstantsAsSet.toArray ++ v.ctors.toArray
  | .ctorInfo v   => ci.getUsedConstantsAsSet.toArray.push v.induct
  | .recInfo v    => ci.getUsedConstantsAsSet.toArray ++ v.all.toArray
  | _             => ci.getUsedConstantsAsSet.toArray

/-- A pure monad over an environment, so core's `collectAxioms` can run outside CoreM. -/
abbrev EnvM := StateM Environment
instance : MonadEnv EnvM where       -- API? field names of `MonadEnv`
  getEnv := get
  modifyEnv f := modify f

/-- True axioms of `n` according to core's `collectAxioms` (uses core's cache for imports). -/
def axiomsOf (env : Environment) (n : Name) : Array Name :=
  ((collectAxioms n : EnvM (Array Name)).run' env)

/-- Hops for every constant solved in this run. -/
abbrev Solved := Std.HashMap Name (Array Hop)

/--
Solve `roots` and everything unresolved they reach. Resolved leaves are axioms
and constants for which `imported` returns entries. `env` must be a view in
which bodies are visible (`setExporting false`).
-/
def solve (axiomsOf : Name → Array Name) (imported : Name → Option (Array Hop))
    (env : Environment) (roots : Array Name) : Solved := Id.run do
  -- 1. discover the unresolved closure
  let mut deps : Std.HashMap Name (Array Name) := {}
  let mut cur  : Std.HashMap Name (Std.HashMap Name Hop) := {}
  let mut seen : NameSet := {}
  let mut stack := roots
  repeat
    match stack.back? with
    | none => break
    | some n =>
      stack := stack.pop
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        if let some hs := imported n then
          let m := hs.foldl (init := ({} : Std.HashMap Name Hop)) fun m h => m.insert h.ax h
          cur := cur.insert n m
        else if let .axiomInfo _ := ci then
          let real := axiomsOf n
          if real.contains n then
            -- a genuine axiom
            cur := cur.insert n (({} : Std.HashMap Name Hop).insert n ⟨n, n, 0⟩)
          else
            -- NOT an axiom: under the module system a definition whose body is
            -- hidden is exposed as `axiomInfo`. Take its true axioms from core's
            -- own cache (`collectAxioms`); no finer provenance is available.
            let m := real.foldl (init := ({} : Std.HashMap Name Hop)) fun m a =>
              m.insert a ⟨a, a, 1⟩
            cur := cur.insert n m
        else
          let ds := directDeps ci
          deps := deps.insert n ds
          for d in ds do
            unless seen.contains d do stack := stack.push d
  -- 2. reverse edges among unresolved nodes
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ds) in deps do
    for d in ds do
      rev := rev.insert d ((rev.getD d #[]).push n)
  -- 3. label-correcting relaxation (distances only decrease ⇒ terminates)
  let mut work : Array Name := deps.fold (fun a n _ => a.push n) #[]
  repeat
    match work.back? with
    | none => break
    | some n =>
      work := work.pop
      let mut m : Std.HashMap Name Hop := cur.getD n {}
      let mut changed := false
      for d in deps.getD n #[] do
        for (ax, h) in cur.getD d {} do
          let nd := h.dist + 1
          match m[ax]? with
          | some o =>
            if nd < o.dist then
              m := m.insert ax ⟨ax, d, nd⟩
              changed := true
          | none =>
            m := m.insert ax ⟨ax, d, nd⟩
            changed := true
      if changed then
        cur := cur.insert n m
        for p in rev.getD n #[] do work := work.push p
  -- 4. report only the nodes solved here
  let mut out : Solved := {}
  for (n, _) in deps do
    let hs := (cur.getD n {}).fold (fun a _ h => a.push h) #[]
    out := out.insert n (hs.qsort (fun a b => a.ax.quickLt b.ax))
  return out

/-- Skip non-visible intermediates: follow `next` until a visible constant. -/
def compressNext (visible : Name → Bool) (solved : Solved) (ax : Name) (h : Hop) : Hop := Id.run do
  let mut n := h.next
  let mut fuel := h.dist
  while fuel > 0 && n != ax && !visible n do
    fuel := fuel - 1
    match (solved[n]?).bind (·.find? (·.ax == ax)) with
    | some h' => n := h'.next
    | none    => break
  return { h with next := n }

/--
The extension. As in core, `asyncMode := .mainOnly`, state = imported entries,
and entries are produced in `exportEntriesFnEx` from the private view.
-/
initialize provExt : PersistentEnvExtension Entry Entry ExtState ←
  registerPersistentEnvExtension {
    mkInitial     := pure {}
    addImportedFn := fun es => pure { importedModuleEntries := es }
    addEntryFn    := fun s _ => s
    asyncMode     := .mainOnly
    exportEntriesFnEx := fun env s =>   -- API? (v4.35.0: takes `env` and `s`)
      let exportedEnv := env.setExporting true
      let privateEnv  := env.setExporting false
      let visible : Name → Bool := fun n => (exportedEnv.find? n).isSome
      let names := env.checked.get.constants.foldStage2 (fun ns n _ => ns.push n) #[]
      let vis := names.filter visible
      let solved := solve (axiomsOf privateEnv) (s.find? env) privateEnv vis
      let entries : Array Entry := vis.filterMap fun n =>
        (solved[n]?).map fun hs =>
          ⟨n, hs.map fun h => compressNext visible solved h.ax h⟩
      .uniform (entries.qsort fun a b => Name.quickLt a.name b.name)
  }

/-! ## Query side -/

/-- Hops of `n`: solved in this run, else imported. -/
def hopsOf (imp : Name → Option (Array Hop)) (res : Solved) (n : Name) : Array Hop :=
  match res[n]? with
  | some hs => hs
  | none    => (imp n).getD #[]

def hopFor? (imp : Name → Option (Array Hop)) (res : Solved) (n ax : Name) : Option Hop :=
  (hopsOf imp res n).find? (·.ax == ax)

/-- Follow `next` pointers from `root` to `ax`. -/
def buildPath (imp : Name → Option (Array Hop)) (res : Solved)
    (root ax : Name) : Array Name := Id.run do
  let mut path := #[root]
  let mut n := root
  let mut fuel := match hopFor? imp res root ax with | some h => h.dist + 1 | none => 0
  while n != ax && fuel > 0 do
    fuel := fuel - 1
    match hopFor? imp res n ax with
    | some h => n := h.next; path := path.push n
    | none   => break
  return path

def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "constructor"
  | .recInfo _    => "recursor"

/-- Find a module's source file via `LEAN_SRC_PATH` (set by `lake env` / `lake build`). -/
def moduleFile (mod : Name) : IO (Option System.FilePath) := do
  let some v ← IO.getEnv "LEAN_SRC_PATH" | return none
  for root in System.SearchPath.parse v do
    let f := modToFilePath root mod "lean"          -- API? `Lean.modToFilePath`
    if ← f.pathExists then return some f
  return none

/-- `file:line [Module]` for a constant. -/
def locate (n : Name) : CoreM String := do
  let env ← getEnv
  let idx? := env.getModuleIdxFor? n
  let mod : Name := match idx? with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none     => env.mainModule
  let line? ← try
      let r ← findDeclarationRanges? n
      pure (r.map (·.range.pos.line))
    catch _ => pure none
  let file? ← (moduleFile mod : IO _)
  let fileStr := match file? with
    | some f => f.toString
    | none   => if idx?.isNone then "<current file>" else s!"<{mod}>"
  let lineStr := match line? with | some l => s!":{l}" | none => ""
  return s!"{fileStr}{lineStr} [{mod}]"

def report (root : Name) : CoreM MessageData := do
  let env ← getEnv
  let penv := env.setExporting false
  let st := provExt.getState (asyncMode := .mainOnly) env
  let imp : Name → Option (Array Hop) := fun n => st.find? env n
  match penv.find? root with
  | none => return m!"unknown constant '{root}'"
  | some rci =>
  if let .axiomInfo _ := rci then
    if (axiomsOf penv root).contains root then
      return m!"'{root}' is itself an axiom  @ {← locate root}"
  let res := solve (axiomsOf penv) imp penv #[root]
  let hops := hopsOf imp res root
  if hops.isEmpty then
    return m!"'{root}' does not depend on any axioms."
  let mut out : Array MessageData := #[]
  out := out.push m!"'{root}' depends on axioms: {hops.toList.map (·.ax)}"
  for h in hops do
    out := out.push m!"\n── {h.ax}  (distance {h.dist})"
    let mut indent := ""
    for n in buildPath imp res root h.ax do
      let k := match penv.find? n with
        | some (.axiomInfo _) =>
          if (axiomsOf penv n).contains n then "axiom"
          else "def, body hidden by module system; axioms taken from core's cache"
        | some ci => kindOf ci
        | none => "?"
      out := out.push m!"{indent}{MessageData.ofConstName n} ({k})  @ {← locate n}"
      indent := indent ++ "  "
  return MessageData.joinSep out.toList "\n"

end AxiomProv

open AxiomProv in
elab "#axiom_blame " ids:ident+ : command => do
  for id in ids do
    for c in ← liftCoreM <| realizeGlobalConstWithInfos id do
      logInfoAt id (← liftCoreM <| report c)
