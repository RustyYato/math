module

public import Math.Algebra.Monoid.Action.Defs
public import Math.Algebra.Semiring.Defs

namespace Math

public class IsModule (R α: Type*)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α]
  extends
    IsRightDistribSMul R α, IsLeftDistribSMul R α,
    IsLawfulMulSMul R α, IsLawfulOneSMul R α where

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsModule ℕ α where
