module

public import Math.Algebra.Monoid.Action.Defs.Basic
public import Math.Algebra.Group.Defs.Basic

import Math.Algebra.Group.Defs.Lemmas

namespace Math

section Basic

public theorem smul_neg
  [AddGroupOps α] [IsAddGroup α]
  [SMul R α] [IsLawfulSMulZero R α] [IsRightDistribSMul R α]
  (r: R) (a: α) : r • (-a) = -(r • a) := by
  apply eq_neg_of_add
  rw [←smul_add, neg_add_cancel, smul_zero]

public theorem neg_smul
  [AddGroupOps R] [IsAddGroup R]
  [AddGroupOps α] [IsAddGroup α]
  [SMul R α] [IsLawfulZeroSMul R α] [IsLeftDistribSMul R α]
  (r: R) (a: α) : (-r) • a = -(r • a) := by
  apply eq_neg_of_add
  rw [←add_smul, neg_add_cancel, zero_smul]

public instance [AddGroupOps α] [IsAddGroup α] [IsAddComm α] : IsRightDistribSMul ℤ α where
  smul_add r a b := zsmul_add a b r
public instance [AddGroupOps α] [IsAddGroup α] : IsLeftDistribSMul ℤ α where
  add_smul r s a := add_zsmul a r s
public instance [AddGroupOps α] [IsAddGroup α] : IsLawfulZeroSMul ℤ α where
  zero_smul := zero_zsmul
public instance [AddGroupOps α] [IsAddGroup α] : IsLawfulSMulZero ℤ α where
  smul_zero := zsmul_zero
public instance [AddGroupOps α] [IsAddGroup α] : IsLawfulOneSMul ℤ α where
  one_smul := one_zsmul
public instance [AddGroupOps α] [IsAddGroup α] : IsLawfulMulSMul ℤ α where
  mul_smul r s a := mul_zsmul a r s
public instance
  [AddGroupOps α] [IsAddGroup α]
  [SMul R α] [IsLawfulSMulZero R α] [IsRightDistribSMul R α]
  : IsSMulComm ℤ R α where
  smul_comm r s a := by
    induction r with
    | ofNat n => dsimp; rw [ofNat_zsmul, ofNat_zsmul, smul_comm]
    | negSucc n => rw [negSucc_zsmul, negSucc_zsmul, smul_neg, smul_comm]
public instance
  [AddGroupOps R] [IsAddGroup R]
  [AddGroupOps α] [IsAddGroup α]
  [SMul R α] [IsLawfulZeroSMul R α] [IsLeftDistribSMul R α]
  : IsScalarTower ℤ R α where
  smul_assoc r s a := by
    cases r with
    | ofNat n => dsimp; rw [ofNat_zsmul, ofNat_zsmul, smul_assoc]
    | negSucc n => rw [negSucc_zsmul, negSucc_zsmul, neg_smul, smul_assoc]
public instance [AddGroupOps α] [IsAddGroup α] : IsScalarTower ℤ ℤ α := inferInstance
public instance [AddGroupOps α] [IsAddGroup α] : IsScalarTower ℕ ℤ α := inferInstance

end Basic
