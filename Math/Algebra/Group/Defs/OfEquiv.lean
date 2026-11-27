module

public import Math.Algebra.Monoid.Defs.OfEquiv
public import Math.Algebra.Group.Defs.Basic

namespace Math.OfEquiv

variable (f: α ≃ β)

public instance [Inv α] [Pow α ℕ] [Pow α ℤ] [IsLawfulPowZ α] : IsLawfulPowZ (OfEquiv f) where
  powz_ofNat a n := by
    induction a with | _ a =>
    simp; rw [powz_ofNat]
  powz_negSucc a n := by
    induction a with | _ a =>
    simp; rw [powz_negSucc]
public instance [Neg α] [SMul ℕ α] [SMul ℤ α] [IsLawfulZSMul α] : IsLawfulZSMul (OfEquiv f) where
  ofNat_zsmul a _ := by
    induction a with | _ a =>
    simp; rw [ofNat_zsmul]
  negSucc_zsmul a n := by
    induction a with | _ a =>
    simp; rw [negSucc_zsmul]
public instance [Mul α] [Inv α] [Div α] [IsLawfulDiv α] : IsLawfulDiv (OfEquiv f) where
  div_eq_mul_inv a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    simp; rw [div_eq_mul_inv]
public instance [Add α] [Neg α] [Sub α] [IsLawfulSub α] : IsLawfulSub (OfEquiv f) where
  sub_eq_add_neg a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    simp; rw [sub_eq_add_neg]
public instance [Mul α] [Inv α] [One α] [IsLawfulInvLeft α] : IsLawfulInvLeft (OfEquiv f) where
  inv_mul_cancel a := by
    induction a with | _ a =>
    simp; rw [inv_mul_cancel]
public instance [Mul α] [Inv α] [One α] [IsLawfulInvRight α] : IsLawfulInvRight (OfEquiv f) where
  mul_inv_cancel a := by
    induction a with | _ a =>
    simp; rw [mul_inv_cancel]
public instance [Add α] [Neg α] [Zero α] [IsLawfulNegLeft α] : IsLawfulNegLeft (OfEquiv f) where
  neg_add_cancel a := by
    induction a with | _ a =>
    simp; rw [neg_add_cancel]
public instance [Add α] [Neg α] [Zero α] [IsLawfulNegRight α] : IsLawfulNegRight (OfEquiv f) where
  add_neg_cancel a := by
    induction a with | _ a =>
    simp; rw [add_neg_cancel]
public instance [GroupOps α] [IsGroup α] : IsGroup (OfEquiv f) where
public instance [AddGroupOps α] [IsAddGroup α] : IsAddGroup (OfEquiv f) where
