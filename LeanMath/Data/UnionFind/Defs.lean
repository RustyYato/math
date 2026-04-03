import LeanMath.Tactic.TypeStar

def safeGet (array: Array (ℕ × ℕ)) (i: ℕ) : ℕ :=
  if h:i < array.size then array[i].fst else i

inductive UnionFind.Spec : Array (ℕ × ℕ) -> ℕ -> Prop where
| root (array: Array (ℕ × ℕ)) (index: ℕ) (hindex: index < array.size) :
  safeGet array index = index -> Spec array index
| step (array: Array (ℕ × ℕ)) (index: ℕ) (hindex: index < array.size) :
  Spec array (safeGet array index) -> Spec array index

structure UnionFind where
  -- entries is an array of (index, rank)
  entries: Array (ℕ × ℕ)
  spec: ∀i < entries.size, UnionFind.Spec entries i
deriving Repr, DecidableEq

def UnionFind.wrap_index (_uf: UnionFind) := ℕ
def UnionFind.wrap_index.mk : ℕ -> wrap_index uf:= id
def UnionFind.wrap_index.get : wrap_index uf -> ℕ := id

def UnionFind.size (uf: UnionFind) : ℕ := uf.entries.size

instance : GetElem UnionFind ℕ ℕ (fun _ _ => True) where
  getElem uf i _ := safeGet uf.entries i

def UnionFind.getElem_of_lt (uf: UnionFind) (i: ℕ) (hi: i < uf.size) : uf[i] = (uf.entries[i]'hi).fst := by
  show (if _:_ then _ else _) = _
  rw [dif_pos]
def UnionFind.getElem_of_ge (uf: UnionFind) (i: ℕ) (hi: uf.size ≤ i) : uf[i] = i := by
  show (if _:_ then _ else _) = _
  rw [dif_neg]
  apply Nat.not_lt_of_le
  assumption

def UnionFind.entry_lt_size (uf: UnionFind) : ∀i < uf.size, uf[i] < uf.size := by
  intro i hi
  cases uf.spec _ hi with
  | root _ _ h =>
    replace h : uf[i] = i := h
    erw [h]; assumption
  | step  _ hi' spec =>
  suffices ∀i, i ∈ uf.entries -> UnionFind.Spec uf.entries i.fst -> i.fst < uf.size by
    let r := uf.entries[i].snd
    apply this (uf[i], r) _ spec
    show (safeGet uf.entries i, _) ∈ _
    unfold safeGet; rw [dif_pos hi']
    apply Array.getElem_mem
  clear hi i spec hi'
  intro (i, r) hi hspec
  cases hspec with
  | root i hi h => dsimp; assumption
  | step i hi' _ => assumption

def UnionFind.wf (uf: UnionFind) : WellFounded (fun a b: ℕ => b < uf.size ∧ a ≠ b ∧ a = uf[b]) := by
  apply WellFounded.intro
  intro a
  apply Acc.intro
  intro b ⟨ha, ne, hb⟩
  induction uf.spec a ha generalizing b with
  | root a ha' h =>
    subst b
    contradiction
  | step a ha' h ih =>
    subst b
    apply Acc.intro
    intro c ⟨hb, ne', hc⟩
    apply ih
    apply uf.entry_lt_size
    assumption
    show c ≠ uf[a]
    assumption
    assumption

instance : WellFoundedRelation (UnionFind.wrap_index uf) where
  rel a b := b.get < uf.size ∧ a.get ≠ b.get ∧ a.get = uf[b.get]
  wf := UnionFind.wf uf

def UnionFind.new (n: ℕ) : UnionFind where
  entries := Array.ofFn (n := n) fun i => (i.val, 0)
  spec i hi := by
    apply Spec.root
    assumption
    unfold safeGet
    rw [dif_pos hi, Array.getElem_ofFn]

def UnionFind.find (uf: UnionFind) (n: ℕ) : ℕ :=
  let m := uf[n]
  if h:m = n then
    n
  else
    uf.find m
termination_by UnionFind.wrap_index.mk (uf := uf) n
decreasing_by
  show n < uf.size ∧ uf[n] ≠ n ∧ uf[n] = uf[n]
  refine ⟨?_, h, rfl⟩
  replace h : safeGet uf.entries n ≠ n := h
  unfold safeGet at h
  split at h
  assumption
  contradiction
