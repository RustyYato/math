import LeanMath.Order.Defs
import LeanMath.Data.Set.Defs

namespace Set

variable [LE α] [LT α]

def upperBounds (s: Set α) : Set α where
  Mem x := ∀a ∈ s, a ≤ x

def lowerBounds (s: Set α) : Set α where
  Mem x := ∀a ∈ s, x ≤ a

def isMaximal (s: Set α) (x: α) : Prop := x ∈ s ∧ ∀a ∈ s, x ≤ a -> a ≤ x
def isMax (s: Set α) (x: α) : Prop := x ∈ s ∧ ∀a ∈ s, a ≤ x
def isMinimal (s: Set α) (x: α) : Prop := x ∈ s ∧ ∀a ∈ s, a ≤ x -> x ≤ a
def isMin (s: Set α) (x: α) : Prop := x ∈ s ∧ ∀a ∈ s, x ≤ a

def IsGLB (s: Set α) (x: α) := s.lowerBounds.isMax x
def IsLUB (s: Set α) (x: α) := s.upperBounds.isMin x

def BoundedAbove (s: Set α) := s.upperBounds.Nonempty
def BoundedBelow (s: Set α) := s.lowerBounds.Nonempty

def Iio (a: α) : Set α where
  Mem x := x < a
def Ioi (a: α) : Set α where
  Mem x := a < x

def Iic (a: α) : Set α where
  Mem x := x ≤ a
def Ici (a: α) : Set α where
  Mem x := a ≤ x

def Icc (a: α) (b: α) : Set α where
  Mem x := a ≤ x ∧ x ≤ b
def Ioo (a: α) (b: α) : Set α where
  Mem x := a < x ∧ x < b

def Ico (a: α) (b: α) : Set α where
  Mem x := a ≤ x ∧ x < b
def Ioc (a: α) (b: α) : Set α where
  Mem x := a < x ∧ x ≤ b

def not_bddAbove_iff [LEM] [IsLinearOrder α] {s: Set α} : ¬s.BoundedAbove ↔ ∀x, ∃a ∈ s, x < a := by
  simp only [BoundedAbove, upperBounds, not_nonempty, eq_empty_iff, ofMem_mem, LEM.not_forall]
  apply Iff.intro
  · intro h x
    have ⟨a, ha, h⟩ := h x
    have := not_le.mp h
    exists a
  · intro h x
    have ⟨a, ha, h⟩ := h x
    have := not_le.mpr h
    exists a
    exists ha

def not_mem_ub_lt_mem_ub
  [LE α] [LT α] [IsPreorder α]
  (U: Set α) (a b: α) (ha: a ∉ U.upperBounds) (hb: b ∈ U.upperBounds) : ¬b ≤ a := by
  intro h; apply ha
  intro x hx
  apply le_trans _ h
  apply hb
  assumption

end Set

instance [SupSet α] : InfSet αᵒᵖ where
  sInf := sSup (α := α)
instance [InfSet α] : SupSet αᵒᵖ where
  sSup := sInf (α := α)

namespace OfEquiv

variable (f: α ≃ β)

instance [SupSet β] : SupSet (OfEquiv f) where
   sSup U := f.symm (⨆ U.preimage f.symm)
instance [InfSet β] : InfSet (OfEquiv f) where
   sInf U := f.symm (⨅ U.preimage f.symm)

@[simp] def sSup_def [SupSet β] (U: Set (OfEquiv f)) : ⨆ U = f.symm (⨆ U.preimage f.symm) := rfl
@[simp] def sInf_def [InfSet β] (U: Set (OfEquiv f)) : ⨅ U = f.symm (⨅ U.preimage f.symm) := rfl

instance [LE β] [SupSet β] [IsLawfulSup β] : IsLawfulSup (OfEquiv f) where
  le_sSup U u hu := by
    dsimp; rw [Equiv.symm_coe]
    apply le_sSup
    apply Set.mem_preimage.mpr
    rwa [Equiv.coe_symm]

instance [LE β] [InfSet β] [IsLawfulInf β] : IsLawfulInf (OfEquiv f) where
  sInf_le U u hu := by
    dsimp; rw [Equiv.symm_coe]
    apply sInf_le
    apply Set.mem_preimage.mpr
    rwa [Equiv.coe_symm]

end OfEquiv
