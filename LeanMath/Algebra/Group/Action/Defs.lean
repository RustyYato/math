import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Algebra.Group.Defs

instance [AddGroupOps α] [IsAddGroup α] : IsMonoidAction ℤ α where
  one_smul a := by rw [one_zsmul]
  mul_smul r s a := by rw [mul_comm, mul_zsmul]

instance [AddGroupOps α] [IsAddGroup α] : IsLawfulSMulZero ℤ α where
  smul_zero r := by rw [zsmul_zero]

instance [AddGroupOps α] [IsAddGroup α] : IsLeftDistribSMul ℤ α where
  add_smul r s a := by rw [add_zsmul]

instance [AddGroupOps α] [IsAddGroup α] : IsLawfulZeroSMul ℤ α where
  zero_smul a := by rw [zero_zsmul]

instance [AddGroupOps α] [IsAddGroup α] [IsAddComm α] : IsDistributiveAction ℤ α where
  smul_add r a b := by rw [zsmul_add]

def neg_smul_left [AddGroupOps R] [AddGroupOps α] [IsAddGroup R] [IsAddGroup α] [SMul R α] [IsLeftDistribSMul R α] [IsLawfulZeroSMul R α] (r: R) (a: α) : -(r • a) = (-r) • a := by
  symm; apply eq_neg_of_add
  rw [←add_smul, neg_add_cancel, zero_smul]

def neg_smul_right [AddGroupOps R] [AddGroupOps α] [IsAddGroup R] [IsAddGroup α] [SMul R α] [IsRightDistribSMul R α] [IsLawfulSMulZero R α] (r: R) (a: α) : -(r • a) = r • (-a) := by
  symm; apply eq_neg_of_add
  rw [←smul_add, neg_add_cancel, smul_zero]

def neg_smul [AddGroupOps α] [IsAddGroup α] [SMul R α]
  [IsRightDistribSMul R α] [IsLawfulSMulZero R α]
  (r: R) (a: α) : r • (-a) = -(r • a) := by
  apply eq_neg_of_add
  rw [←smul_add, neg_add_cancel, smul_zero]

instance
  [AddGroupOps R] [IsAddGroup R]
  [AddGroupOps α] [IsAddGroup α]
  [SMul R α] [IsLeftDistribSMul R α]
  [IsLawfulZeroSMul R α]
  : IsScalarTower ℤ R α where
  smul_assoc r s a := by
    cases r with
    | ofNat r => rw [ofNat_zsmul, ofNat_zsmul, smul_assoc]
    | negSucc r => rw [negSucc_zsmul, negSucc_zsmul, ←neg_smul_left, smul_assoc]

instance [AddGroupOps α] [IsAddGroup α] : IsScalarTower ℕ ℤ α := inferInstance
instance [AddGroupOps α] [IsAddGroup α] : IsScalarTower ℤ ℤ α := inferInstance

def smul_neg [AddGroupOps α] [IsAddGroup α] [SMul R α]
  [IsRightDistribSMul R α] [IsLawfulSMulZero R α]
  (r: R) (a: α) : r • (-a) = -(r • a) := by
  apply eq_neg_of_add
  rw [←smul_add, neg_add_cancel, smul_zero]

def smul_sub [AddGroupOps α] [IsAddGroup α] [SMul R α]
  [IsRightDistribSMul R α] [IsLawfulSMulZero R α]
  (r: R) (a b: α) : r • (a - b) = r • a - r • b := by
  rw [sub_eq_add_neg, smul_add, smul_neg, ←sub_eq_add_neg]

instance [SMul R α] [AddGroupOps α] [IsAddGroup α] [IsRightDistribSMul R α] [IsLawfulSMulZero R α] : IsSMulComm ℤ R α where
  smul_comm r s a := by
    cases r with
    | ofNat r => rw [ofNat_zsmul, ofNat_zsmul, smul_comm]
    | negSucc r => rw [negSucc_zsmul, negSucc_zsmul, smul_comm, smul_neg]

section

variable [SMul R α] [Add α] [SMul R β] [AddGroupOps β] [IsAddComm β] [IsAddGroup β] [IsLawfulSMulZero R β] [IsSMulComm R R β] [IsRightDistribSMul R β]

instance : Neg (α →ₗ[R] β) where
  neg f := {
    toFun x := -f x
    map_smul := by
      intro r' a
      rw [smul_neg, map_smul]
    map_add a b := by
      rw [map_add, neg_add_rev, add_comm]
  }

instance : Sub (α →ₗ[R] β) where
  sub f g := LinearHom.copy (f + -g) (fun x => f x - g x) <| by
    intro x; dsimp
    rw [sub_eq_add_neg]; rfl

instance : IsAddGroup (α →ₗ[R] β) where
  sub_eq_add_neg _ _ := by
    apply DFunLike.ext; intro x
    apply sub_eq_add_neg
  ofNat_zsmul _ _ := by
    apply DFunLike.ext; intro x
    apply ofNat_zsmul
  negSucc_zsmul _ _ := by
    apply DFunLike.ext; intro x
    apply negSucc_zsmul
  add_neg_cancel _ := by
    apply DFunLike.ext; intro x
    apply add_neg_cancel

end

variable
  [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β]
  [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β]

instance : IsSMulHom F ℤ α β where
  map_smul f r a := by
    cases r
    rw [ofNat_zsmul, ofNat_zsmul, map_smul]
    rw [negSucc_zsmul, negSucc_zsmul,
      map_neg, map_smul]
