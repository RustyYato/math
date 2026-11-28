module

public import Math.Algebra.Monoid.Defs.Hom
public import Math.Algebra.Group.Defs.Basic
import Math.Algebra.Monoid.Defs.Lemmas

namespace Math

namespace Automorphism

variable [MonoidOps α] [IsMonoid α] [AddMonoidOps α] [IsAddMonoid α]

public scoped instance : Inv (α ≃* α) where
  inv := .symm
public scoped instance : Div (α ≃* α) where
  div a b := a * b⁻¹

public scoped instance : Pow (α ≃* α) ℤ where
  pow a z := match z with
    | .ofNat z => a ^ z
    | .negSucc z => (a ^ (z + 1))⁻¹

public scoped instance : IsGroup (α ≃* α) where
  div_eq_mul_inv _ _ := rfl
  powz_ofNat _ _ := rfl
  powz_negSucc _ _ := rfl
  inv_mul_cancel _ := by ext; apply GroupEquiv.apply_symm

public scoped instance : Inv (α ≃+ α) where
  inv := .symm
public scoped instance : Div (α ≃+ α) where
  div a b := a * b⁻¹

public scoped instance : Pow (α ≃+ α) ℤ where
  pow a z := match z with
    | .ofNat z => a ^ z
    | .negSucc z => (a ^ (z + 1))⁻¹

public scoped instance : IsGroup (α ≃+ α) where
  div_eq_mul_inv _ _ := rfl
  powz_ofNat _ _ := rfl
  powz_negSucc _ _ := rfl
  inv_mul_cancel _ := by ext; apply AddGroupEquiv.apply_symm

end Automorphism

section

public theorem map_inv
  [Funlike F α β]
  [Mul α] [One α] [Inv α] [IsLawfulInvLeft α]
  [GroupOps β] [IsGroup β]
  [IsMulHom F α β] [IsOneHom F α β]
  (f: F) (a: α) : f (a⁻¹) = (f a)⁻¹ := by
  apply eq_inv_of_mul
  rw [←map_mul, inv_mul_cancel, map_one]

public theorem map_neg
  [Funlike F α β]
  [Add α] [Zero α] [Neg α] [IsLawfulNegLeft α]
  [AddGroupOps β] [IsAddGroup β]
  [IsAddHom F α β] [IsZeroHom F α β]
  (f: F) (a: α) : f (-a) = -f a :=
  map_inv (MulOfAdd.mk f) (MulOfAdd.mk a)

public theorem map_div
  [Funlike F α β]
  [Mul α] [One α] [Inv α] [Div α] [IsLawfulInvLeft α] [IsLawfulDiv α]
  [GroupOps β] [IsGroup β]
  [IsMulHom F α β] [IsOneHom F α β]
  (f: F) (a b: α) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_inv]

public theorem map_sub
  [Funlike F α β]
  [Add α] [Zero α] [Neg α] [Sub α] [IsLawfulNegLeft α] [IsLawfulSub α]
  [AddGroupOps β] [IsAddGroup β]
  [IsAddHom F α β] [IsZeroHom F α β]
  (f: F) (a b: α) : f (a - b) = f a - f b :=
  map_div (MulOfAdd.mk f) (MulOfAdd.mk a) (MulOfAdd.mk b)

public theorem map_powz
  [Funlike F α β]
  [GroupOps α] [GroupOps β]
  [IsLawfulPowN α] [IsLawfulPowZ α]
  [IsLawfulInvLeft α] [IsGroup β]
  [IsMulHom F α β] [IsOneHom F α β]
  (f: F) (a: α) (n: ℤ) : f (a ^ n) = f a ^ n := by
  cases n with
  | ofNat n => dsimp; rw [powz_ofNat, powz_ofNat, map_pown]
  | negSucc n => rw [powz_negSucc, powz_negSucc, map_inv, map_pown]

public theorem map_zsmul
  [Funlike F α β]
  [AddGroupOps α] [AddGroupOps β]
  [IsLawfulNSMul α] [IsLawfulZSMul α]
  [IsLawfulNegLeft α] [IsAddGroup β]
  [IsAddHom F α β] [IsZeroHom F α β]
  (f: F) (a: α) (n: ℤ) : f (n • a) = n • f a :=
  map_powz (MulOfAdd.mk f) (MulOfAdd.mk a) n

end

theorem subNatNat_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) (n m: ℕ) : (Int.subNatNat n m) • a = n • a - m • a := by
  unfold Int.subNatNat
  split <;> rename_i k h; clear k; dsimp
  · rw [ofNat_zsmul, ←sub_nsmul_add _ _ _ (Nat.le_of_sub_eq_zero h),
      sub_eq_add_neg _ (m • a), add_assoc, add_neg_cancel, add_zero]
  · rw [negSucc_zsmul, ←show m - n = k + 1 from h]
    apply neg_eq_of_add
    rw [sub_eq_add_neg  _ (m • a),
      ←add_assoc, sub_nsmul_add, add_neg_cancel]
    apply Nat.le_of_lt
    apply Nat.lt_of_sub_pos
    rw [h]; apply Nat.zero_lt_succ

@[expose] public def zsmul_hom [AddGroupOps α] [IsAddGroup α] (a: α) : ℤ →+ α where
  toFun n := n • a
  map_zero := by
    show ((0: ℕ): ℤ) • a = 0
    rw [ofNat_zsmul, zero_nsmul]
  map_add n m := by
    rcases n with n | n <;> rcases m with m | m
    any_goals dsimp
    · rw [Int.ofNat_add_ofNat]
      iterate 3 rw [ofNat_zsmul]
      rw [add_nsmul]
    · rw [Int.ofNat_add_negSucc, subNatNat_zsmul, negSucc_zsmul, ofNat_zsmul, sub_eq_add_neg]
    · rw [Int.negSucc_add_ofNat, subNatNat_zsmul, negSucc_zsmul, ofNat_zsmul, add_comm, sub_eq_add_neg]
    · rw [Int.negSucc_add_negSucc]
      iterate 3 rw [negSucc_zsmul]
      apply neg_eq_of_add
      rw [←Nat.succ_add, add_assoc, add_comm n.succ, add_nsmul,
        ←add_assoc, add_assoc ((m + 1) • _),
          add_neg_cancel, add_zero, add_neg_cancel]

@[expose] public def powz_hom [GroupOps α] [IsGroup α] (a: α) : ℤ →ₘ+ α where
  toFun n := a ^ n
  map_zero_to_one := map_zero (β := AddOfMul α) (zsmul_hom (AddOfMul.mk a))
  map_add_to_mul := map_add (β := AddOfMul α) (zsmul_hom (AddOfMul.mk a))
