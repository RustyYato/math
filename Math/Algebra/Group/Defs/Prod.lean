module

public import Math.Algebra.Monoid.Defs.Prod
public import Math.Algebra.Group.Defs.Basic

namespace Math

variable {ι α β: Type*} {γ: ι -> Type*}

section Mul

public instance [Inv α] [Inv β] : Inv (α × β) where
  inv a := (a.fst⁻¹, a.snd⁻¹)

public instance [Div α] [Div β] : Div (α × β) where
  div a b := (a.fst / b.fst, a.snd / b.snd)

public instance [One α] [One β] [Inv α] [Inv β] [Mul α] [Mul β] [IsLawfulInvLeft α] [IsLawfulInvLeft β] : IsLawfulInvLeft (α × β) where
  inv_mul_cancel a := by ext <;> apply inv_mul_cancel
public instance [One α] [One β] [Inv α] [Inv β] [Mul α] [Mul β] [IsLawfulInvRight α] [IsLawfulInvRight β] : IsLawfulInvRight (α × β) where
  mul_inv_cancel a := by ext <;> apply mul_inv_cancel
public instance [Inv α] [Inv β] [Mul α] [Mul β] [Div α] [Div β] [IsLawfulDiv α] [IsLawfulDiv β] : IsLawfulDiv (α × β) where
  div_eq_mul_inv  _ _ := by ext <;> apply div_eq_mul_inv
public instance [Inv α] [Inv β] [Pow α ℕ] [Pow β ℕ] [Pow α ℤ] [Pow β ℤ] [IsLawfulPowZ α] [IsLawfulPowZ β] : IsLawfulPowZ (α × β) where
  powz_ofNat _ _ := by ext <;> apply powz_ofNat
  powz_negSucc _ _ := by ext <;> apply powz_negSucc

public instance [GroupOps α] [GroupOps β] [IsGroup α] [IsGroup β] : IsGroup (α × β) where

public instance [∀i, Inv (γ i)] : Inv (∀i, γ i) where
  inv a _ := (a _)⁻¹

public instance [∀i, Div (γ i)] : Div (∀i, γ i) where
  div a b _ := a _ / b _

public instance [∀i, One (γ i)] [∀i, Inv (γ i)] [∀i, Mul (γ i)] [∀i, IsLawfulInvLeft (γ i)] : IsLawfulInvLeft (∀i, γ i) where
  inv_mul_cancel a := by ext <;> apply inv_mul_cancel
public instance [∀i, One (γ i)] [∀i, Inv (γ i)] [∀i, Mul (γ i)] [∀i, IsLawfulInvRight (γ i)] : IsLawfulInvRight (∀i, γ i) where
  mul_inv_cancel a := by ext <;> apply mul_inv_cancel
public instance [∀i, Inv (γ i)] [∀i, Mul (γ i)] [∀i, Div (γ i)] [∀i, IsLawfulDiv (γ i)] : IsLawfulDiv (∀i, γ i) where
  div_eq_mul_inv  _ _ := by ext <;> apply div_eq_mul_inv
public instance [∀i, Inv (γ i)] [∀i, Pow (γ i) ℕ] [∀i, Pow (γ i) ℤ] [∀i, IsLawfulPowZ (γ i)] : IsLawfulPowZ (∀i, γ i) where
  powz_ofNat _ _ := by ext <;> apply powz_ofNat
  powz_negSucc _ _ := by ext <;> apply powz_negSucc

public instance [∀i, GroupOps (γ i)] [∀i, IsGroup (γ i)] : IsGroup (∀i, γ i) where

public instance [Inv α] : Inv (ι -> α) := inferInstance
public instance [Div α] : Div (ι -> α) := inferInstance
public instance [One α] [Inv α] [Mul α] [IsLawfulInvLeft α] : IsLawfulInvLeft (ι -> α) := inferInstance
public instance [One α] [Inv α] [Mul α] [IsLawfulInvRight α] : IsLawfulInvRight (ι -> α) := inferInstance
public instance [Inv α] [Mul α] [Div α] [IsLawfulDiv α] : IsLawfulDiv (ι -> α) := inferInstance
public instance [Inv α] [Pow α ℕ] [Pow α ℤ] [IsLawfulPowZ α] : IsLawfulPowZ (ι -> α) := inferInstance
public instance [GroupOps α] [IsGroup α] : IsGroup (ι -> α) := inferInstance

end Mul

section Add

public instance [Neg α] [Neg β] : Neg (α × β) where
  neg a := (-a.fst, -a.snd)

public instance [Sub α] [Sub β] : Sub (α × β) where
  sub a b := (a.fst - b.fst, a.snd - b.snd)

public instance [Zero α] [Zero β] [Neg α] [Neg β] [Add α] [Add β] [IsLawfulNegLeft α] [IsLawfulNegLeft β] : IsLawfulNegLeft (α × β) where
  neg_add_cancel a := by ext <;> apply neg_add_cancel
public instance [Zero α] [Zero β] [Neg α] [Neg β] [Add α] [Add β] [IsLawfulNegRight α] [IsLawfulNegRight β] : IsLawfulNegRight (α × β) where
  add_neg_cancel a := by ext <;> apply add_neg_cancel
public instance [Neg α] [Neg β] [Add α] [Add β] [Sub α] [Sub β] [IsLawfulSub α] [IsLawfulSub β] : IsLawfulSub (α × β) where
  sub_eq_add_neg  _ _ := by ext <;> apply sub_eq_add_neg
public instance [Neg α] [Neg β] [SMul ℕ α] [SMul ℕ β] [SMul ℤ α] [SMul ℤ β] [IsLawfulZSMul α] [IsLawfulZSMul β] : IsLawfulZSMul (α × β) where
  ofNat_zsmul _ _ := by ext <;> apply ofNat_zsmul
  negSucc_zsmul _ _ := by ext <;> apply negSucc_zsmul

public instance [GroupOps α] [GroupOps β] [IsGroup α] [IsGroup β] : IsGroup (α × β) where

public instance [∀i, Neg (γ i)] : Neg (∀i, γ i) where
  neg a _ := -a _

public instance [∀i, Sub (γ i)] : Sub (∀i, γ i) where
  sub a b _ := a _ - b _

public instance [∀i, Zero (γ i)] [∀i, Neg (γ i)] [∀i, Add (γ i)] [∀i, IsLawfulNegLeft (γ i)] : IsLawfulNegLeft (∀i, γ i) where
  neg_add_cancel a := by ext <;> apply neg_add_cancel
public instance [∀i, Zero (γ i)] [∀i, Neg (γ i)] [∀i, Add (γ i)] [∀i, IsLawfulNegRight (γ i)] : IsLawfulNegRight (∀i, γ i) where
  add_neg_cancel a := by ext <;> apply add_neg_cancel
public instance [∀i, Neg (γ i)] [∀i, Add (γ i)] [∀i, Sub (γ i)] [∀i, IsLawfulSub (γ i)] : IsLawfulSub (∀i, γ i) where
  sub_eq_add_neg  _ _ := by ext <;> apply sub_eq_add_neg
public instance [∀i, Neg (γ i)] [∀i, SMul ℕ (γ i)] [∀i, SMul ℤ (γ i)] [∀i, IsLawfulZSMul (γ i)] : IsLawfulZSMul (∀i, γ i) where
  ofNat_zsmul _ _ := by ext <;> apply ofNat_zsmul
  negSucc_zsmul _ _ := by ext <;> apply negSucc_zsmul

public instance [∀i, GroupOps (γ i)] [∀i, IsGroup (γ i)] : IsGroup (∀i, γ i) where

public instance [Neg α] : Neg (ι -> α) := inferInstance
public instance [Sub α] : Sub (ι -> α) := inferInstance
public instance [Zero α] [Neg α] [Add α] [IsLawfulNegLeft α] : IsLawfulNegLeft (ι -> α) := inferInstance
public instance [Zero α] [Neg α] [Add α] [IsLawfulNegRight α] : IsLawfulNegRight (ι -> α) := inferInstance
public instance [Neg α] [Add α] [Sub α] [IsLawfulSub α] : IsLawfulSub (ι -> α) := inferInstance
public instance [Neg α] [SMul ℕ α] [SMul ℤ α] [IsLawfulZSMul α] : IsLawfulZSMul (ι -> α) := inferInstance
public instance [GroupOps α] [IsGroup α] : IsGroup (ι -> α) := inferInstance

end Add
