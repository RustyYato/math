import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.AddMonoidWithOne.Set

structure Subsemiring (α: Type*) [Add α] [Mul α] [Zero α] [One α] extends AddSubMonoidWithOne α, SubMonoid α where

instance [Add α] [Mul α] [Zero α] [One α] : SetLike (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemMul (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemAdd (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemOne (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemZero (Subsemiring α) α where

section

variable (s: S) [SetLike S α] [Add α] [Mul α] [IsMemAdd S α] [IsMemMul S α]

instance [IsLeftDistrib α] : IsLeftDistrib s where
  mul_add _ _ _ := by
    apply Subtype.val_inj
    apply mul_add

instance [IsRightDistrib α] : IsRightDistrib s where
  add_mul _ _ _ := by
    apply Subtype.val_inj
    apply add_mul

end

variable (s: S) [SetLike S α] [SemiringOps α] [IsSemiring α] [IsMemAdd S α] [IsMemMul S α] [IsMemOne S α] [IsMemZero S α]

instance : IsSemiring s where
