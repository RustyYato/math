import LeanMath.Algebra.Monoid.Action
import LeanMath.Algebra.Semiring.Defs

class IsModule (R α: Type*)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α]
  : Prop extends IsDistributiveAction R α, IsLeftDistribSMul R α where

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsModule ℕ α where
