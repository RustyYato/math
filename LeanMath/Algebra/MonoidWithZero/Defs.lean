import LeanMath.Algebra.Monoid.Defs

class IsMonoidWithZero (α: Type*) [MonoidOps α] [Zero α] : Prop extends IsMonoid α, IsLawfulZeroMul α where

variable [MonoidOps α] [Zero α] [IsMonoidWithZero α]

def zero_npow (n: ℕ) (hn: 0 < n) : (0: α) ^ n = 0 := by
  cases n; contradiction
  rw [npow_succ, mul_zero]
