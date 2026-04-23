import LeanMath.Algebra.Monoid.Defs

class IsMonoidWithZero (α: Type*) [MonoidOps α] [Zero α] : Prop extends IsMonoid α, IsLawfulZeroMul α where

variable [MonoidOps α] [Zero α] [IsMonoidWithZero α]

def zero_npow_succ (n: ℕ) : (0: α) ^ (n + 1) = 0 := by
  rw [npow_succ, mul_zero]

def zero_npow (n: ℕ) (hn: 0 < n) : (0: α) ^ n = 0 := by
  cases n; contradiction
  rw [zero_npow_succ]

instance : IsMonoidWithZero ℕ where
instance : IsMonoidWithZero ℤ where

namespace OfEquiv

variable (f: α ≃ β)

protected scoped instance [Zero β] [MonoidOps β] [IsMonoidWithZero β] : IsMonoidWithZero (OfEquiv f) where

end OfEquiv
