import LeanMath.Data.Set.Defs

class Topology (α: Type*) where
  -- the set of open sets
  protected IsOpen : Set α -> Prop
  protected open_univ: IsOpen ⊤
  protected open_sUnion (U: Set (Set α)) (hU: ∀u ∈ U, IsOpen u) : IsOpen (⋃ U)
  protected open_inter (a b: Set α) (ha: IsOpen a) (hb: IsOpen b) : IsOpen (a ∩ b)

namespace Topology

variable {α β: Type*} [Topology α] [Topology β]

def OpenSets (α: Type*) [Topology α] : Set (Set α) where
  Mem := Topology.IsOpen
def OpenSets.univ : ⊤ ∈ OpenSets α := Topology.open_univ
def OpenSets.inter {a b: Set α} : a ∈ OpenSets α -> b ∈ OpenSets α -> a ∩ b ∈ OpenSets α := Topology.open_inter _ _
def OpenSets.sUnion {U: Set (Set α)} : (∀u ∈ U, u ∈ OpenSets α) -> ⋃ U ∈ OpenSets α := Topology.open_sUnion _
def OpenSets.empty : ⊥ ∈ OpenSets α := by
  rw [←Set.sUnion_empty]
  apply sUnion
  nofun

def ClosedSets (α: Type*) [Topology α] : Set (Set α) where
  Mem s := sᶜ ∈ OpenSets α
def ClosedSets.univ : ⊤ ∈ ClosedSets α := by
  show ⊤ᶜ ∈ OpenSets α
  simp; apply OpenSets.empty
def ClosedSets.empty : ⊥ ∈ ClosedSets α := by
  show ⊥ᶜ ∈ OpenSets α
  simp; apply OpenSets.univ
def ClosedSets.sInter (U: Set (Set α)) (hU: ∀u ∈ U, u ∈ ClosedSets α) : ⋂ U ∈ ClosedSets α := by
  show _ᶜ ∈ OpenSets α
  simp; apply OpenSets.sUnion
  intro u hu
  simp at hu
  have : _ ∈ OpenSets α := hU _ hu
  simpa using this
def ClosedSets.union {a b: Set α} : a ∈ ClosedSets α -> b ∈ ClosedSets α -> a ∪ b ∈ ClosedSets α := by
  intro ha hb
  show _ᶜ ∈ OpenSets α
  simp; apply OpenSets.inter
  assumption
  assumption

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

instance IsContinuous.const (x: β) : IsContinuous (fun _: α => x) where
  isOpen_preimage s sopen := by
    by_cases h:x ∈ s
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

instance : Top (Topology α) where
  top := {
    IsOpen := IsTrivial
    open_univ := IsTrivial.univ
    open_sUnion := by
      intro U hU
      by_cases htop:⊤ ∈ U
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

inductive Generate (U: Set (Set α)) : Set a -> Prop where
| of (u: Set α) : u ∈ U -> Generate U u
| univ : Generate U ⊤
| inter {a b: Set α} : Generate U a -> Generate U b -> Generate U (a ∩ b)
| sUnion {V: Set (Set α)} : (∀v ∈ V, Generate U v) -> Generate U (⋃ V)

def generate (U: Set (Set α)) : Topology α where
  IsOpen := Generate U
  open_univ := Generate.univ
  open_sUnion _ := Generate.sUnion
  open_inter _ _ := Generate.inter

end Topology
