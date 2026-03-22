import LeanMath.Data.Set.Defs
import LeanMath.Order.CompleteLattice

class Topology (α: Type*) where
  -- the set of open sets
  protected IsOpen : Set α -> Prop
  protected open_univ: IsOpen ⊤
  protected open_sUnion (U: Set (Set α)) (hU: ∀u ∈ U, IsOpen u) : IsOpen (⋃ U)
  protected open_inter (a b: Set α) (ha: IsOpen a) (hb: IsOpen b) : IsOpen (a ∩ b)

namespace Topology

def OpenSets (α: Type*) [Topology α] : Set (Set α) where
  Mem := Topology.IsOpen
def OpenSets_inj (α: Type*): Function.Injective (α := Topology α) (fun a => a.OpenSets) := by
  intro a b h
  cases a; cases b; congr
  cases h; rfl
def OpenSets.univ {_: Topology α} : ⊤ ∈ OpenSets α := Topology.open_univ
def OpenSets.inter {_: Topology α} {a b: Set α} : a ∈ OpenSets α -> b ∈ OpenSets α -> a ∩ b ∈ OpenSets α := Topology.open_inter _ _
def OpenSets.sUnion {_: Topology α} {U: Set (Set α)} : (∀u ∈ U, u ∈ OpenSets α) -> ⋃ U ∈ OpenSets α := Topology.open_sUnion _
def OpenSets.empty {_: Topology α} : ⊥ ∈ OpenSets α := by
  rw [←Set.sUnion_empty]
  apply sUnion
  nofun

def ClosedSets (α: Type*) [Topology α] : Set (Set α) where
  Mem s := sᶜ ∈ OpenSets α
def ClosedSets.univ {_: Topology α} : ⊤ ∈ ClosedSets α := by
  show ⊤ᶜ ∈ OpenSets α
  simp; apply OpenSets.empty
def ClosedSets.empty {_: Topology α} : ⊥ ∈ ClosedSets α := by
  show ⊥ᶜ ∈ OpenSets α
  simp; apply OpenSets.univ
def ClosedSets.sInter {_: Topology α} (U: Set (Set α)) (hU: ∀u ∈ U, u ∈ ClosedSets α) : ⋂ U ∈ ClosedSets α := by
  show _ᶜ ∈ OpenSets α
  simp; apply OpenSets.sUnion
  intro u hu
  simp at hu
  have : _ ∈ OpenSets α := hU _ hu
  simpa using this
def ClosedSets.union {_: Topology α} {a b: Set α} : a ∈ ClosedSets α -> b ∈ ClosedSets α -> a ∪ b ∈ ClosedSets α := by
  intro ha hb
  show _ᶜ ∈ OpenSets α
  simp; apply OpenSets.inter
  assumption
  assumption

variable {α β: Type*} [Topology α] [Topology β]

-- the interior of a set is the union of all open subsets
def Interior (U: Set α) : Set α := ⋃ (OpenSets α ∩ U.powerset)
-- the closure of a set is the intersection fo all closed supersets
def Closure (U: Set α) : Set α := ⋂ (ClosedSets α ∩ Set.ofMem (U ⊆ ·))

class IsContinuous (f : α → β) : Prop where
  isOpen_preimage : ∀s ∈ OpenSets β, s.preimage f ∈ OpenSets α

def OpenSets.preimage (f: α -> β) [IsContinuous f] : ∀s ∈ OpenSets β, s.preimage f ∈ OpenSets α :=
  IsContinuous.isOpen_preimage

def IsOpen.Interior (s: Set α) : Interior s ∈ OpenSets α := by
  apply OpenSets.sUnion
  intro x hx
  exact hx.left

instance IsContinuous.const [LEM] (x: β) : IsContinuous (fun _: α => x) where
  isOpen_preimage s sopen := by
    rcases em (x ∈ s) with h | h
    suffices s.preimage (fun _: α => x) = (⊤: Set α) by
      rw [this]
      apply OpenSets.univ
    apply Set.ext_univ
    intro
    assumption
    suffices s.preimage (fun _: α => x) = ∅ by
      rw [this]
      apply OpenSets.empty
    apply Set.ext_empty
    intro
    assumption

def instDiscrete : Topology α where
  IsOpen _ := True
  open_univ := True.intro
  open_sUnion _ _ := True.intro
  open_inter _ _ _ _ := True.intro

inductive IsTrivial : Set α -> Prop where
| empty : IsTrivial ⊥
| univ : IsTrivial ⊤

instance [LEM] : Top (Topology α) where
  top := {
    IsOpen := IsTrivial
    open_univ := IsTrivial.univ
    open_sUnion := by
      intro U hU
      rcases em (⊤ ∈ U) with htop | htop
      rw [show ⋃ U = ⊤ from ?_]; apply IsTrivial.univ
      ext; simp; exists ⊤
      rw [show ⋃ U = ⊥ from ?_]; apply IsTrivial.empty
      ext; simp
      intro x hx g
      cases hU x hx
      contradiction
      contradiction
    open_inter := by
      intro a b ha hb
      cases ha <;> cases hb
      all_goals simp
      iterate 3 apply IsTrivial.empty
      apply IsTrivial.univ
  }

instance : Bot (Topology α) where
  bot := instDiscrete

instance : Topology ℕ := instDiscrete
instance : Topology ℤ := instDiscrete

inductive Generate (U: Set (Set α)) : Set α -> Prop where
| of (u: Set α) : u ∈ U -> Generate U u
| univ : Generate U ⊤
| inter {a b: Set α} : Generate U a -> Generate U b -> Generate U (a ∩ b)
| sUnion {V: Set (Set α)} : (∀v ∈ V, Generate U v) -> Generate U (⋃ V)

def generate (U: Set (Set α)) : Topology α where
  IsOpen := Generate U
  open_univ := Generate.univ
  open_sUnion _ := Generate.sUnion
  open_inter _ _ := Generate.inter

def of_mem_generate
  {γ: Type u}
  {a: Set γ} {U: Set (Set γ)}
  (h: a ∈ (generate U).OpenSets)
  (t: Topology γ)
  (ht: ∀x ∈ U, x ∈ t.OpenSets) : a ∈ t.OpenSets := by
  replace h : Generate U a := h
  induction h with
  | of => apply ht; assumption
  | univ => apply OpenSets.univ
  | inter => apply OpenSets.inter <;> assumption
  | sUnion => apply OpenSets.sUnion <;> assumption

def mem_generate_of
  {γ: Type u}
  {a: Set γ} {U: Set (Set γ)}
  (h: a ∈ U) : a ∈ (generate U).OpenSets := by
  apply Generate.of
  assumption

instance : InfSet (Topology α) where
  sInf U := generate (⋃ (U.image (fun t => t.OpenSets)))

instance : Min (Topology α) where
  min a b := generate (a.OpenSets ∪ b.OpenSets)

instance : SupSet (Topology α) where
  sSup U := {
    IsOpen a := a ∈ sInf (U.image (fun t => t.OpenSets))
    open_univ := by
      rintro _ ⟨t, ht, rfl⟩
      apply OpenSets.univ
    open_sUnion := by
      rintro V hV _ ⟨t, ht, rfl⟩
      apply OpenSets.sUnion
      intro u hu
      apply hV u hu
      apply Set.mem_image'
      assumption
    open_inter := by
      rintro a b ha hb _ ⟨t, ht, rfl⟩
      apply OpenSets.inter
      apply ha
      apply Set.mem_image'
      assumption
      apply hb
      apply Set.mem_image'
      assumption
  }

instance : Max (Topology α) where
  max a b := {
    IsOpen x := x ∈ a.OpenSets ∩ b.OpenSets
    open_univ := by
      apply And.intro
      apply OpenSets.univ
      apply OpenSets.univ
    open_sUnion := by
      intro U hU
      apply And.intro
      apply OpenSets.sUnion
      intro u hu
      exact (hU u hu).left
      apply OpenSets.sUnion
      intro u hu
      exact (hU u hu).right
    open_inter := by
      intro x y hx hy
      apply And.intro
      apply OpenSets.inter
      exact hx.left
      exact hy.left
      apply OpenSets.inter
      exact hx.right
      exact hy.right
  }

def max_eq_sSup (a b: Topology α) : a ⊔ b = sSup {a, b} := by
  apply OpenSets_inj
  show _ ∩ _ = sInf _
  simp

def min_eq_sInf (a b: Topology α) : a ⊓ b = sInf {a, b} := by
  show generate _ = generate _
  congr
  simp

instance : LE (Topology α) where
  le a b := b.OpenSets ⊆ a.OpenSets
instance : LT (Topology α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

variable [LEM]

def mem_sSup (a: Set α) (U: Set (Topology α)) :
  a ∈ (sSup U).OpenSets ↔ ∀t ∈ U, a ∈ t.OpenSets := by
  apply Iff.intro
  rintro ha t ht
  exact ha t.OpenSets (Set.mem_image' ht)
  rintro ht _ ⟨_, _, rfl⟩
  apply ht
  assumption

private protected def sInf_le (U: Set (Topology α)) (u: (Topology α)) (hu: u ∈ U) : ⨅ U ≤ u := by
  intro x hx
  apply mem_generate_of
  refine ⟨u.OpenSets, ?_, ?_⟩
  apply Set.mem_image'
  assumption
  assumption
private protected def le_sInf (U: Set (Topology α)) (x: (Topology α)) : (∀u ∈ U, x ≤ u) -> x ≤ ⨅ U := by
  intro hx a ha
  apply of_mem_generate ha
  intro _ ⟨_, ⟨t, ht, rfl⟩, hx'⟩
  apply hx
  assumption
  assumption
private protected def le_sSup (U: Set (Topology α)) (u: (Topology α)) (hu: u ∈ U) : u ≤ ⨆ U := by
  intro a b
  rw [mem_sSup] at b
  apply b
  assumption
private protected def sSup_le (U: Set (Topology α)) (x: (Topology α)) : (∀u ∈ U, u ≤ x) -> ⨆ U ≤ x := by
  intro h b
  rw [mem_sSup]
  intro _ _ _
  apply h
  assumption
  assumption

instance : IsCompleteLattice (Topology α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl _ := Set.sub_refl _
  trans := flip Set.sub_trans
  antisymm {a b} ha hb := by
    apply OpenSets_inj
    apply Set.sub_antisymm <;> assumption
  max_le := by
    intro x a b ha hb
    rw [max_eq_sSup]
    apply sSup_le
    intro u hu
    simp at hu
    rcases hu with rfl | rfl <;> assumption
  left_le_max := by
    intro a b
    rw [max_eq_sSup]
    apply le_sSup
    simp
  right_le_max := by
    intro a b
    rw [max_eq_sSup]
    apply le_sSup
    simp
  min_le_left := by
    intro a b
    rw [min_eq_sInf]
    apply sInf_le
    simp
  min_le_right := by
    intro a b
    rw [min_eq_sInf]
    apply sInf_le
    simp
  le_min := by
    intro x a b ha hb
    rw [min_eq_sInf]
    apply le_sInf
    simp [ha, hb]
  sInf_le := sInf_le
  le_sInf := le_sInf
  le_sSup := le_sSup
  sSup_le := sSup_le
  le_top := by
    intro a _ h
    cases h
    apply OpenSets.empty
    apply OpenSets.univ
  bot_le := by
    intro _ _ _
    trivial

end Topology
