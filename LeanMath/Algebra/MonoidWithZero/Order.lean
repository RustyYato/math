import LeanMath.Algebra.MonoidWithZero.Defs
import LeanMath.Algebra.Monoid.Order

class IsOrderedZeroMul (α: Type*) [LE α] [LT α] [Mul α] [Zero α] extends IsLawfulZeroMul α where
  protected mul_nonneg: ∀{a b: α}, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b
  protected mul_le_mul_of_nonneg_left: ∀{a b: α}, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b
  protected mul_le_mul_of_nonneg_right: ∀{a b: α}, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c

instance [LE α] [LT α] [MonoidOps α] [Zero α] [IsLawfulZeroMul α] [IsZeroLEOne α] [IsOrderedCommMonoid α] : IsOrderedZeroMul α where
  mul_nonneg {a b} ha hb := by
    rw [←mul_zero 0]
    apply mul_le_mul
    assumption
    assumption
  mul_le_mul_of_nonneg_left {a b} h k hk := by
    apply mul_le_mul_left
    assumption
  mul_le_mul_of_nonneg_right  {a b} h k hk := by
    apply mul_le_mul_right
    assumption

instance : IsOrderedZeroMul ℕ := inferInstance
instance : IsOrderedZeroMul ℤ where
  mul_nonneg := Int.mul_nonneg
  mul_le_mul_of_nonneg_left {_ _} h _:= Int.mul_le_mul_of_nonneg_left h
  mul_le_mul_of_nonneg_right {_ _} h _:= Int.mul_le_mul_of_nonneg_right h

section

variable [LE α] [LT α] [Mul α] [Zero α] [IsOrderedZeroMul α]

def mul_nonneg: ∀{a b: α}, 0 ≤ a -> 0 ≤ b -> 0 ≤ a * b := IsOrderedZeroMul.mul_nonneg
def mul_le_mul_of_nonneg_left: ∀{a b: α}, a ≤ b -> ∀c, 0 ≤ c -> c * a ≤ c * b := IsOrderedZeroMul.mul_le_mul_of_nonneg_left
def mul_le_mul_of_nonneg_right: ∀{a b: α}, a ≤ b -> ∀c, 0 ≤ c -> a * c ≤ b * c := IsOrderedZeroMul.mul_le_mul_of_nonneg_right

end

namespace OfEquiv

variable (f: α ≃ β)

protected scoped instance [LE β] [LT β] [Mul β] [Zero β] [IsOrderedZeroMul β] : IsOrderedZeroMul (OfEquiv f) where
  mul_nonneg {a b} ha hb := by
    dsimp at *
    rw [Equiv.symm_coe] at *
    rw [Equiv.symm_coe]
    apply mul_nonneg <;> assumption
  mul_le_mul_of_nonneg_left {a b} h k hk := by
    dsimp at *
    rw [Equiv.symm_coe] at *
    rw [Equiv.symm_coe]
    apply mul_le_mul_of_nonneg_left <;> assumption
  mul_le_mul_of_nonneg_right {a b} h k hk := by
    dsimp at *
    rw [Equiv.symm_coe] at *
    rw [Equiv.symm_coe]
    apply mul_le_mul_of_nonneg_right <;> assumption

end OfEquiv
