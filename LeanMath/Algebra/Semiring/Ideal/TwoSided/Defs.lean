import LeanMath.Algebra.Semiring.Ideal.Defs

structure Ideal (α: Type*) [SemiringOps α] [IsSemiring α] extends AddSubMonoid α, SubLeftMul α, SubRightMul α, SubZero α where

variable [SemiringOps α] [IsSemiring α]

instance : SetLike (Ideal α) α where
instance : IsMemAdd (Ideal α) α where
instance : IsMemLeftMul (Ideal α) α where
instance : IsMemRightMul (Ideal α) α where
instance : IsMemZero (Ideal α) α where
