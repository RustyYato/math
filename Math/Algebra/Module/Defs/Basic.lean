module

public import Math.Algebra.Monoid.Action.Defs.Basic
public import Math.Algebra.Semiring.Defs.Basic

namespace Math

public class IsModule (R α: Type*)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α]
  extends
    IsRightDistribSMul R α, IsLeftDistribSMul R α,
    IsLawfulMulSMul R α, IsLawfulOneSMul R α,
    IsLawfulZeroSMul R α, IsLawfulSMulZero R α where

public instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsModule ℕ α where

public instance [Add α] [Mul α] [IsRightDistrib α] : IsLeftDistribSMul α α where
  add_smul _ _ _ := add_mul _ _ _
public instance [Add α] [Mul α] [IsLeftDistrib α] : IsRightDistribSMul α α where
  smul_add _ _ _ := mul_add _ _ _
public instance [SemiringOps α] [IsSemiring α] : IsModule α α where

namespace OfEquiv

variable (f: α ≃ β)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α] [IsModule R α]

public instance : IsModule R (OfEquiv f) where

end OfEquiv
