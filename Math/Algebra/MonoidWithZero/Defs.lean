module

public import Math.Algebra.Monoid.Defs

namespace Math

public class IsMonoidWithZero (α: Type*) [MonoidOps α] [Zero α] : Prop extends IsMonoid α, IsLawfulZeroMul α where

variable [MonoidOps α] [Zero α] [IsMonoidWithZero α]

public theorem zero_pown_succ (n: ℕ) : (0: α) ^ (n + 1) = 0 := by
  rw [pown_succ, mul_zero]

public theorem zero_pown (n: ℕ) (hn: 0 < n) : (0: α) ^ n = 0 := by
  cases n
  nomatch hn
  rw [zero_pown_succ]

public instance : IsMonoidWithZero ℕ where
public instance : IsMonoidWithZero ℤ where
