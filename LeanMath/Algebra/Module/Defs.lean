import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Algebra.Semiring.Defs

class IsModule (R α: Type*)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α]
  : Prop extends IsDistributiveAction R α, IsLeftDistribSMul R α, IsLawfulZeroSMul R α where

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsModule ℕ α where


variable [SemiringOps R] [IsSemiring R] [Add α] [SMul R α] [AddMonoidOps β] [IsAddMonoid β]
  [IsAddComm β] [SMul R β] [IsSMulComm R R β] [IsModule R β]

instance : IsModule R (α →ₗ[R] β) where
  add_smul _ _ _ := by
    apply DFunLike.ext; intro x
    apply add_smul
  zero_smul _ := by
    apply DFunLike.ext; intro x
    apply zero_smul
