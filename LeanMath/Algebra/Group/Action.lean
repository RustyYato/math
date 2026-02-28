import LeanMath.Algebra.Monoid.Action
import LeanMath.Algebra.Group.Defs

instance [AddGroupOps α] [IsAddGroup α] : IsMonoidAction ℤ α where
  one_smul a := by rw [one_zsmul]
  mul_smul r s a := by rw [mul_comm, mul_zsmul]

instance [AddGroupOps α] [IsAddGroup α] : IsLawfulSMulZero ℤ α where
  smul_zero r := by rw [zsmul_zero]

instance [AddGroupOps α] [IsAddGroup α] : IsLeftDistribSMul ℤ α where
  add_smul r s a := by rw [add_zsmul]

instance [AddGroupOps α] [IsAddGroup α] [IsAddComm α] : IsDistributiveAction ℤ α where
  smul_add r a b := by rw [zsmul_add]

instance [AddGroupOps α] [IsAddGroup α] : IsScalarTower ℕ ℤ α where
  smul_assoc r s a := by
    show (r * s) • a = _
    rw [mul_comm, mul_zsmul, ofNat_zsmul]

instance [AddGroupOps α] [IsAddGroup α] : IsScalarTower ℤ ℤ α where
  smul_assoc r s a := by
    show (r * s) • a = _
    rw [mul_comm, mul_zsmul]
