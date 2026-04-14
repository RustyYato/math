import LeanMath.Data.Equiv.Basic
import LeanMath.Tactic.PPWithUniv

@[pp_with_univ]
inductive ZFSet.Pre : Type (u + 1) where
| intro (ι: Type u) (mem: ι -> ZFSet.Pre)

def ZFSet.Pre.«Type» : ZFSet.Pre.{u} -> Type u
| .intro ι _ => ι

@[coe]
def ZFSet.Pre.Mem : ∀s: ZFSet.Pre, s.Type -> ZFSet.Pre
| .intro _ mem => mem

@[simp] def ZFSet.Pre.mk_Type (ι: Type u) (mem: ι -> ZFSet.Pre) :  (intro ι mem).Type = ι := rfl
@[simp] def ZFSet.Pre.mk_Mem (ι: Type u) (mem: ι -> ZFSet.Pre) :  (intro ι mem).Mem = mem := rfl

inductive ZFSet.EquivState.{u} where
| intro (a b: ZFSet.Pre.{u})
| exists_left (a b: ZFSet.Pre.{u}) (a₀: a.Type)
| exists_right (a b: ZFSet.Pre.{u}) (b₀: b.Type)

inductive ZFSet.PreEquiv : ZFSet.EquivState.{u} -> Prop where
| intro (a b: ZFSet.Pre.{u}) :
  (∀a₀, PreEquiv (.exists_left a b a₀)) ->
  (∀b₀, PreEquiv (.exists_right a b b₀)) ->
  PreEquiv (.intro a b)
| equiv_left (a b: ZFSet.Pre.{u}) (a₀: a.Type) (b₀: b.Type) :
  PreEquiv (.intro (a.Mem a₀) (b.Mem b₀)) ->
  PreEquiv (.exists_left a b a₀)
| equiv_right (a b: ZFSet.Pre.{u}) (a₀: a.Type) (b₀: b.Type) :
  PreEquiv (.intro (a.Mem a₀) (b.Mem b₀)) ->
  PreEquiv (.exists_right a b b₀)

instance : HasEquiv ZFSet.Pre.{u} where
  Equiv a b := ZFSet.PreEquiv (.intro a b)

def ZFSet.Pre.Equiv.intro
  (a b: ZFSet.Pre.{u})
  (hfwd: ∀i: a.Type, ∃j: b.Type, a.Mem i ≈ b.Mem j)
  (hrev: ∀j: b.Type, ∃i: a.Type, a.Mem i ≈ b.Mem j) :
  a ≈ b := by
  cases a with | _ a amem =>
  cases b with | _ b bmem =>
  apply ZFSet.PreEquiv.intro
  · intro i
    have ⟨j, h⟩ := hfwd i
    apply PreEquiv.equiv_left
    apply h
  · intro j
    have ⟨i, h⟩ := hrev j
    apply PreEquiv.equiv_right
    apply h

@[induction_eliminator]
def ZFSet.Pre.Equiv.rec {motive: ∀a b: ZFSet.Pre, a ≈ b -> Prop}
  (intro: ∀(a b: ZFSet.Pre)
    (hfwd: ∀i: a.Type, ∃(j: b.Type) (h: a.Mem i ≈ b.Mem j), motive _ _ h)
    (hrev: ∀j: b.Type, ∃(i: a.Type) (h: a.Mem i ≈ b.Mem j), motive _ _ h),
    motive a b (ZFSet.Pre.Equiv.intro a b (by
      intro i; have ⟨j, h, _⟩ := hfwd i; exists j) (by
      intro i; have ⟨j, h, _⟩ := hrev i; exists j)))
  {a b: ZFSet.Pre} (h: a ≈ b) : motive a b h := by
  have ab: ZFSet.PreEquiv _ := h
  show motive a b ab
  induction a generalizing b with | _ α αmem ih =>
  cases b with | _ β βmem =>
  cases ab with | _ _ _ fwd rev =>
  dsimp at fwd rev
  apply intro <;> dsimp
  · intro i
    cases fwd i with | _ _ _ _ j =>
    refine ⟨j, ?_, ?_⟩
    assumption
    apply ih
    assumption
  · intro i
    cases rev i with | _ _ _ j =>
    refine ⟨j, ?_, ?_⟩
    assumption
    apply ih
    assumption

@[cases_eliminator]
def ZFSet.Pre.Equiv.cases {motive: ∀a b: ZFSet.Pre, a ≈ b -> Prop}
  (intro: ∀(a b: ZFSet.Pre)
    (fwd: ∀i: a.Type, ∃(j: b.Type), a.Mem i ≈ b.Mem j)
    (rev: ∀j: b.Type, ∃(i: a.Type), a.Mem i ≈ b.Mem j),
    motive a b (ZFSet.Pre.Equiv.intro a b fwd rev))
  {a b: ZFSet.Pre} (h: a ≈ b) : motive a b h := by
  induction h with | _ a b fwd rev =>
  apply intro
  intro i; have ⟨j, _, _⟩ := fwd i; exists j
  intro i; have ⟨j, _, _⟩ := rev i; exists j

def ZFSet.PreEquiv.fwd
  {a b: ZFSet.Pre} (h: a ≈ b) : ∀i: a.Type, ∃(j: b.Type), a.Mem i ≈ b.Mem j := by
  cases h
  assumption
def ZFSet.PreEquiv.rev
  {a b: ZFSet.Pre} (h: a ≈ b) : ∀j: b.Type, ∃(i: a.Type), a.Mem i ≈ b.Mem j := by
  cases h
  assumption

@[refl]
def ZFSet.Pre.Equiv.refl (s: ZFSet.Pre) : s ≈ s := by
  induction s with
  | intro ι mem ih =>
  apply Pre.Equiv.intro
  iterate 2
  intro i; exists i; apply ih

@[symm]
def ZFSet.Pre.Equiv.symm {s t: ZFSet.Pre} : s ≈ t -> t ≈ s := by
  intro h
  induction h with
  | intro a b fwd rev =>
  apply intro
  intro i; have ⟨j, h, _⟩ := rev i; exists j
  intro i; have ⟨j, h, _⟩ := fwd i; exists j

def ZFSet.Pre.Equiv.trans {s t u: ZFSet.Pre} : s ≈ t -> t ≈ u -> s ≈ u := by
  intro h g
  induction h generalizing u with
  | intro a b fwd₀ rev₀ =>
  cases g with
  | intro _ c fwd₁ rev₁ =>
  apply intro
  · intro i
    have ⟨j, hj, ih⟩ := fwd₀ i
    have ⟨k, hk⟩ := fwd₁ j
    exists k
    apply ih
    assumption
  · intro i
    have ⟨k, hk⟩ := rev₁ i
    have ⟨j, hj, ih⟩ := rev₀ k
    exists j
    apply ih
    assumption

instance ZFSet.Pre.setoid : Setoid ZFSet.Pre where
  r a b := a ≈ b
  iseqv := {
    refl := ZFSet.Pre.Equiv.refl
    symm := ZFSet.Pre.Equiv.symm
    trans := ZFSet.Pre.Equiv.trans
  }

@[refl]
def ZFSet.Pre.Equiv.refl' (s: ZFSet.Pre) : instHasEquivOfSetoid.Equiv s s := by
  apply ZFSet.Pre.Equiv.refl

@[pp_with_univ]
structure ZFSet.{u} where
  ofQuot :: toQuot : Quotient ZFSet.Pre.setoid.{u}

namespace ZFSet

def ofPre : ZFSet.Pre -> ZFSet := ZFSet.ofQuot ∘ Quotient.mk _

@[induction_eliminator]
def ind {motive: ZFSet -> Prop} (ofPre: ∀a: ZFSet.Pre, motive (ofPre a)) : ∀s, motive s := by
  intro ⟨s⟩; induction s using Quotient.ind with | _ s =>
  apply ofPre

def sound {a b: ZFSet.Pre} : a ≈ b -> ofPre a = ofPre b := by
  intro h
  unfold ofPre
  dsimp; rw [Quotient.sound h]

def exact {a b: ZFSet.Pre} : ofPre a = ofPre b -> a ≈ b := by
  intro h
  exact Quotient.exact (ZFSet.ofQuot.inj h)

def lift (f: ZFSet.Pre -> α) (h: ∀a b, a ≈ b -> f a = f b) (a: ZFSet) : α := a.toQuot.liftOn f h
def lift₂ (f: ZFSet.Pre -> ZFSet.Pre -> α) (h: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: ZFSet) : α := a.toQuot.liftOn₂ b.toQuot f h

instance : Membership Pre Pre where
  mem s t := ∃i, s.Mem i ≈ t

instance : Membership ZFSet ZFSet where
  mem := lift₂ Membership.mem <| by
    suffices ∀a b c d: Pre, a ≈ c -> b ≈ d -> b ∈ a -> d ∈ c by
      intro a b c d h g
      apply propext; apply Iff.intro
      apply this; assumption; assumption
      apply this; symm; assumption; symm; assumption
    intro a b c d ac bd h
    obtain ⟨i, h⟩ := h
    have ⟨j, ac⟩ := ac.fwd i
    exists j
    apply Pre.Equiv.trans _ bd
    apply Pre.Equiv.trans _ h
    symm; assumption

instance : HasSubset ZFSet where
  Subset a b := ∀x, x ∈ a -> x ∈ b

@[ext] def ext (a b: ZFSet) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := by
  induction a with | _ a =>
  induction b with | _ b =>
  replace h : ∀x, x ∈ a ↔ x ∈ b := fun x => h (ofPre x)
  cases a with | _ a fa =>
  cases b with | _ b fb =>
  apply sound;
  apply Pre.Equiv.intro
  · intro i
    have ⟨j, hj⟩ := (h (fa i)).mp ⟨i, by dsimp; apply Pre.Equiv.refl⟩
    exists j
    symm; assumption
  · intro i
    have ⟨j, hj⟩ := (h (fb i)).mpr ⟨i, by dsimp; apply Pre.Equiv.refl⟩
    exists j

instance : EmptyCollection ZFSet where
  emptyCollection := ofPre (Pre.intro PEmpty nofun)

@[simp] def not_mem_empty (s: ZFSet) : ¬s ∈ (∅: ZFSet) := by
  induction s with | _ s =>
  nofun

def eq_empty {s: ZFSet} : s = ∅ ↔ ∀x, x ∉ s := by
  apply Iff.intro
  intro rfl; simp
  intro h
  ext; simp ; apply h

def Pre.union (a b: Pre.{u}) : Pre := .intro (a.Type ⊕ b.Type) (fun
  | .inl x => a.Mem x
  | .inr x => b.Mem x)

instance : Union Pre where
  union := .union

instance : Union ZFSet where
  union := lift₂ (fun a b => ofPre (a ∪ b)) <| by
    intro a b c d ac bd
    apply sound
    cases ac with | _ _ _ ac ca =>
    cases bd with | _ _ _ bd db =>
    apply Pre.Equiv.intro
    · intro i
      rcases i with i | i
      have ⟨j, _⟩ := ac i
      exists .inl j
      have ⟨j, _⟩ := bd i
      exists .inr j
    · intro i
      rcases i with i | i
      have ⟨j, _⟩ := ca i
      exists .inl j
      have ⟨j, _⟩ := db i
      exists .inr j

@[simp] def mem_union {a b: ZFSet} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x
  induction a with | _ a =>
  induction b with | _ b =>
  induction x with | _ x =>
  apply Iff.intro
  · intro h
    obtain ⟨i, h⟩ := h
    rcases i with i | i
    left; exists i
    right; exists i
  · intro h
    rcases h with ⟨i, h⟩ | ⟨i, h⟩
    exists .inl i
    exists .inr i

def Pre.sep (P: Pre -> Prop) (a: Pre) : Pre :=
  .intro { x // P (a.Mem x) } (fun x => a.Mem x)

def sep (P: ZFSet -> Prop) : ZFSet -> ZFSet :=
  lift (fun p => ofPre <| p.sep (P ∘ ofPre)) <| by
    intro a b h
    apply sound
    apply Pre.Equiv.intro
    · intro ⟨i, hi⟩
      have ⟨j, hj⟩ := h.fwd i
      dsimp at hi
      rw [sound hj] at hi
      exists ⟨j, hi⟩
    · intro ⟨i, hi⟩
      have ⟨j, hj⟩ := h.rev i
      dsimp at hi
      rw [←sound hj] at hi
      exists ⟨j, hi⟩

@[simp] def mem_sep {P: ZFSet -> Prop} {a: ZFSet} : ∀{x}, x ∈ a.sep P ↔ x ∈ a ∧ P x := by
  intro x
  induction a with | _ a =>
  induction x with | _ x =>
  apply Iff.intro
  · intro ⟨⟨j, hj⟩, h⟩
    apply And.intro
    exists j
    rw [←sound h]
    assumption
  · intro ⟨⟨j, hj⟩, h⟩
    rw [←sound hj] at h
    exists ⟨j, h⟩

instance : Inter ZFSet where
  inter a b := a.sep (· ∈ b)

@[simp] def mem_inter {a b: ZFSet} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := mem_sep

instance : SDiff ZFSet where
  sdiff a b := a.sep (· ∉ b)

@[simp] def mem_sdiff {a b: ZFSet} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := mem_sep

def Pre.powerset (p: Pre.{u}) : Pre.{u} :=
  .intro (p.Type -> Prop) fun P =>
    .intro { i // P i } fun x => p.Mem x.val

def powerset : ZFSet -> ZFSet :=
  lift (ofPre ∘ Pre.powerset) <| by
    intro a b h; apply sound
    apply Pre.Equiv.intro
    · intro P
      refine ⟨?_, ?_⟩
      intro x; exact (∃i: a.Type, P i ∧ a.Mem i ≈ b.Mem x)
      apply Pre.Equiv.intro
      · intro ⟨i, hi⟩
        have ⟨j, h⟩ := h.fwd i
        exists ⟨j, ?_⟩
        dsimp; exists i
        assumption
      · intro ⟨j, i, _, hi⟩
        exists ⟨i, ?_⟩
        assumption
    · intro P
      refine ⟨?_, ?_⟩
      intro x; exact (∃j: b.Type, P j ∧ a.Mem x ≈ b.Mem j)
      apply Pre.Equiv.intro
      · intro ⟨j, i, _, hi⟩
        exists ⟨i, ?_⟩
        assumption
      · intro ⟨i, hi⟩
        have ⟨j, h⟩ := h.rev i
        exists ⟨j, ?_⟩
        dsimp; exists i
        assumption

@[simp] def mem_powerset {a: ZFSet} : ∀{x}, x ∈ a.powerset ↔ x ⊆ a := by
  intro x
  induction a with | _ A =>
  induction x with | _ X =>
  apply Iff.intro
  · intro h z hz
    induction z with | _ Z =>
    have ⟨x, hx⟩ := hz
    have ⟨P, hP⟩ := h
    have ⟨⟨a, Pa⟩, ha⟩ := hP.rev x
    exists a
    apply Pre.Equiv.trans ha
    assumption
  · intro sub
    refine ⟨fun a => ∃x: X.Type, A.Mem a ≈ X.Mem x, ?_⟩
    apply Pre.Equiv.intro
    · intro ⟨a, x, ha⟩
      exists x
    · intro x
      have ⟨a, ha⟩ := sub (ofPre (X.Mem x)) ⟨x, Pre.Equiv.refl _⟩
      exists ⟨a, x, ha⟩

def Pre.singleton (a: Pre) : Pre := .intro PUnit (fun _ => a)

instance : Singleton ZFSet.{u} ZFSet.{u} where
  singleton := lift (ofPre ∘ Pre.singleton) <| by
    intro a b h; apply sound
    apply Pre.Equiv.intro
    intro i; exists PUnit.unit
    intro i; exists PUnit.unit

@[simp] def mem_singleton {a: ZFSet} : ∀{x}, x ∈ ({a}: ZFSet) ↔ x = a := by
  intro x
  induction a with | _ A =>
  induction x with | _ X =>
  apply Iff.intro
  · intro ⟨_, _⟩
    symm; apply sound
    assumption
  · intro h
    have := exact h
    exists PUnit.unit
    symm; assumption

def eq_singleton {a: ZFSet} : ∀x: ZFSet, x = {a} ↔ ∀y, y ∈ x ↔ y = a := by
  intro x
  apply Iff.intro
  intro rfl; simp
  intro h
  ext y; simp
  apply Iff.intro <;> simp [h]

instance : Insert ZFSet ZFSet where
  insert x a := {x} ∪ a

@[simp] def mem_insert {a b: ZFSet} : ∀{x}, x ∈ insert b a ↔ x = b ∨ x ∈ a := by simp [insert]

protected def Nonempty (a: ZFSet) : Prop := ∃x, x ∈ a

def Pre.sUnion (A: Pre) : Pre :=
  .intro (Σa: A.Type, (A.Mem a).Type) fun x =>
    (A.Mem x.fst).Mem x.snd

def sUnion : ZFSet -> ZFSet :=
  lift (ofPre ∘ Pre.sUnion) <| by
    intro a b h
    apply sound
    apply Pre.Equiv.intro
    · intro ⟨i, i'⟩
      have ⟨j, h⟩ := h.fwd i
      have ⟨j', h⟩ := h.fwd i'
      exists ⟨j, j'⟩
    · intro ⟨i, i'⟩
      have ⟨j, h⟩ := h.rev i
      have ⟨j', h⟩ := h.rev i'
      exists ⟨j, j'⟩

@[simp] def mem_sUnion {a: ZFSet} : ∀{x}, x ∈ a.sUnion ↔ ∃a' ∈ a, x ∈ a' := by
  intro x
  induction a with | _ A =>
  induction x with | _ X =>
  apply Iff.intro
  · intro h
    obtain ⟨⟨i, i'⟩, h⟩ := h
    refine ⟨ofPre (A.Mem i), ?_, ?_⟩
    exists i; apply Pre.Equiv.refl
    exists i'
  · intro ⟨B, hB, h⟩
    induction B with | _ B =>
    obtain ⟨a, ha⟩ := hB
    obtain ⟨b, hb⟩ := h
    have ⟨a', ha'⟩ := ha.rev b
    refine ⟨⟨a, a'⟩, ?_⟩
    apply Pre.Equiv.trans _ hb
    assumption

def sInter (a: ZFSet) : ZFSet := a.sUnion.sep (fun x => ∀b ∈ a, x ∈ b)

def mem_sInter {a: ZFSet} (ha: a.Nonempty) : ∀{x}, x ∈ a.sInter ↔ ∀b ∈ a, x ∈ b := by
  obtain ⟨b, hb⟩ := ha
  intro x
  simp [sInter]
  intro h
  exists b; apply And.intro
  assumption
  apply h
  assumption

@[simp] def upair_copy (a: ZFSet) : {a, a} = ({a}: ZFSet) := by ext x; simp

@[simp] def singleton_ne_empty (a: ZFSet) : {a} ≠ (∅: ZFSet) := by
  intro h
  have : a ∈ (∅: ZFSet) := by simp [←h]
  simp at this

@[simp] def insert_ne_empty (a b: ZFSet) : insert a b ≠ ∅ := by
  intro h
  have : a ∈ (∅: ZFSet) := by simp [←h]
  simp at this

@[simp] def singleton_inj (a b: ZFSet) : {a} = ({b}: ZFSet) ↔ a = b := by
  apply flip Iff.intro; intro rfl; rfl
  intro h
  have : a ∈ ({b}: ZFSet) := by simp [←h]
  simpa using this

@[simp] def insert_eq_singleton (a b c: ZFSet) : insert a b = {c} ↔ a = c ∧ b ⊆ {c} := by
  apply Iff.intro
  intro h
  have : a ∈ ({c}: ZFSet) := by simp [←h]
  simp at this; apply And.intro this
  intro x hx
  rw[←h]
  simp [hx]
  intro ⟨rfl, hb⟩
  ext x; simp
  rw [←mem_singleton]
  apply hb

def pair (l r: ZFSet.{u}) : ZFSet := {{{}, l}, {r}}

def pair_inj {a b c d: ZFSet} : pair a b = pair c d -> a = c ∧ b = d := by
  intro hpair; unfold pair at hpair
  suffices a = c by
    apply And.intro this; subst c
    have h₀ : {d} ∈ ({{∅, a}, {b}}: ZFSet) := by simp [hpair]
    have h₁ : {b} ∈ ({{∅, a}, {d}}: ZFSet) := by simp [←hpair]
    simp at h₀; rcases h₀ with this | this
    simp [Eq.comm] at this
    obtain ⟨rfl, this⟩ := this
    simp at h₁; rcases h₁ with this | this
    simp [Eq.comm] at this
    exact this.left
    simpa using this
    exact this.symm
  have h₀ : {{}, a} ∈ ({{∅, c}, {d}}: ZFSet) := by simp [←hpair]
  have h₁ : {{}, c} ∈ ({{∅, a}, {b}}: ZFSet) := by simp [hpair]
  simp at h₀; rcases h₀ with h | h
  have : a ∈ ({{}, c}: ZFSet) := by simp [←h]
  simp at this; rcases this with rfl | rfl
  simp [Eq.comm] at h
  symm; simpa using h c
  rfl
  have := h.right a
  simp at this; subst d
  cases h.left
  simp at h₁; rcases h₁ with h₁ | h₁
  symm; simpa using h₁ c
  cases h₁.left
  symm; simpa using h₁.right c

def IsUnorderedPair (f: ZFSet) : Prop := ∃l r, f = {l, r}
def IsOrderedPair (f: ZFSet) : Prop := ∃l r, f = pair l r

def IsMapping (f: ZFSet) : Prop := ∀x ∈ f, x.IsOrderedPair
def IsFunction (f: ZFSet) : Prop :=
  f.IsMapping ∧
  -- each input has at most one output
  ∀d r₀ r₁, pair d r₀ ∈ f -> pair d r₁ ∈ f -> r₀ = r₁

def IsInjection (f: ZFSet) : Prop :=
  f.IsMapping ∧
  -- each output has at most one input
  ∀d₀ d₁ r, pair d₀ r ∈ f -> pair d₁ r ∈ f -> d₀ = d₁

def domain (f: ZFSet) : ZFSet := f.sUnion.sUnion.sep fun d => ∃r, pair d r ∈ f

def range (f: ZFSet) : ZFSet := f.sUnion.sUnion.sep fun r => ∃d, pair d r ∈ f

@[simp] def mem_domain {f: ZFSet} : ∀{x}, x ∈ f.domain ↔ ∃r, pair x r ∈ f := by
  intro x
  simp [domain]
  intro r h
  exists {{}, x}; simp
  exists pair x r
  apply And.intro h
  simp [pair]

@[simp] def mem_range {f: ZFSet} : ∀{x}, x ∈ f.range ↔ ∃d, pair d x ∈ f := by
  intro x
  simp [range]
  intro d hd
  exists {x}
  apply And.intro
  exists pair d x
  apply And.intro hd
  simp [pair]
  simp

def image (f: ZFSet) (s: ZFSet) : ZFSet := f.range.sep fun r => ∃d ∈ s, pair d r ∈ f

@[simp] def mem_image {f: ZFSet} {s: ZFSet} : ∀{x}, x ∈ f.image s ↔ ∃d ∈ s, pair d x ∈ f := by
  intro x
  simp [image]
  intro d hd h
  exists d

private noncomputable def reify' (f: ZFSet) (hf: IsFunction f) : ∀d ∈ f.domain, { s // pair d s ∈ f } :=
  fun d hd =>
    have : existsUnique fun r => pair d r ∈ f := by
      have ⟨r, hr⟩ := ZFSet.mem_domain.mp hd
      exists r; dsimp
      apply And.intro hr
      intro r' hr'
      exact hf.right _ _ _ hr hr'
    {
      val := Classical.choose_unique this
      property := Classical.choose_unique_spec this
    }

noncomputable def reify (f: ZFSet) (hf: IsFunction f) : ∀d ∈ f.domain, ZFSet := fun d hd => (reify' f hf d hd).val

def reify_spec (f: ZFSet) (hf: IsFunction f) : ∀d hd, pair d (reify f hf d hd) ∈ f := fun _ _ => (reify' _ _ _ _).property

end ZFSet
