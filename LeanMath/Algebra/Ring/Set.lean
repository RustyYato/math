import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.AddGroupWithOne.Set
import LeanMath.Algebra.Semiring.Set

structure Subring (α: Type*) [Add α] [Mul α] [Neg α] [Zero α] [One α] extends AddSubgroupWithOne α, Subsemiring α where

instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : SetLike (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemMul (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemAdd (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemNeg (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemOne (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemZero (Subring α) α where

variable (s: S) [SetLike S α] [RingOps α] [IsRing α] [IsMemAdd S α] [IsMemMul S α] [IsMemNeg S α] [IsMemOne S α] [IsMemZero S α]

instance : RingOps s where

instance : IsRing s where
