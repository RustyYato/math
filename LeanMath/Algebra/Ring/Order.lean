import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Semiring.Order
import LeanMath.Algebra.Group.Order

variable [LE α] [LT α] [RingOps α] [IsRing α] [IsOrderedZeroMul α]
  [IsOrderedAddCommMonoid α]

def mul_nonpos_of_nonpos_of_nonneg: ∀{a b: α}, a ≤ 0 -> 0 ≤ b -> a * b ≤ 0 := by
  intro a b ha hb
  rw [←neg_neg (a * b), neg_mul_left, ←neg_zero]
  apply neg_le_neg
  apply mul_nonneg
  rw [←neg_zero]
  apply neg_le_neg
  assumption
  assumption
def mul_nonpos_of_nonneg_of_nonpos: ∀{a b: α}, 0 ≤ a -> b ≤ 0 -> a * b ≤ 0 := by
  intro a b ha hb
  rw [←neg_neg (a * b), neg_mul_right, ←neg_zero]
  apply neg_le_neg
  apply mul_nonneg
  assumption
  rw [←neg_zero]
  apply neg_le_neg
  assumption
