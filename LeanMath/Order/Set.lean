import LeanMath.Order.Defs
import LeanMath.Data.Set.Defs

namespace Set

variable [LE α] [LT α]

def upperBounds (s: Set α) : Set α where
  Mem x := ∀a ∈ s, a ≤ x

def lowerBounds (s: Set α) : Set α where
  Mem x := ∀a ∈ s, x ≤ a

def isMaximal (s: Set α) (x: α) : Prop := ∀a ∈ s, x ≤ a -> a ≤ x
def isMax (s: Set α) (x: α) : Prop := ∀a ∈ s, a ≤ x
def isMinimal (s: Set α) (x: α) : Prop := ∀a ∈ s, a ≤ x -> x ≤ a
def isMin (s: Set α) (x: α) : Prop := ∀a ∈ s, x ≤ a

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

end Set

instance [SupSet α] : InfSet αᵒᵖ where
  sInf := sSup (α := α)
instance [InfSet α] : SupSet αᵒᵖ where
  sSup := sInf (α := α)
