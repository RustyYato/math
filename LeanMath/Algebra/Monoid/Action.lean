import LeanMath.Algebra.Action.Defs
import LeanMath.Algebra.Monoid.Defs

class IsMonoidAction (R α: Type*) [MonoidOps R] [IsMonoid R] [SMul R α]
  : Prop extends IsLawfulOneSMul R α, IsLawfulMulSMul R α where

class IsDistributiveAction (R α: Type*)
  [MonoidOps R] [IsMonoid R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α]
  : Prop extends IsMonoidAction R α, IsLawfulSMulZero R α, IsRightDistribSMul R α where

instance [AddMonoidOps α] [IsAddMonoid α] : IsMonoidAction ℕ α where
  one_smul a := by rw [one_nsmul]
  mul_smul r s a := by rw [mul_comm, mul_nsmul]

instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulSMulZero ℕ α where
  smul_zero r := by rw [nsmul_zero]

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsDistributiveAction ℕ α where
  smul_add r a b := by rw [nsmul_add]

instance [AddMonoidOps α] [IsAddMonoid α] : IsLeftDistribSMul ℕ α where
  add_smul r s a := by rw [add_nsmul]

instance [AddMonoidOps α] [IsAddMonoid α] : IsScalarTower ℕ ℕ α where
  smul_assoc r s a := by
    show (r * s) • a = _
    rw [mul_comm, mul_nsmul]
