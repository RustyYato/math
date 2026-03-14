import LeanMath.Algebra.Group.Defs
import LeanMath.Algebra.Monoid.Func

variable {ι: Type*} {A: ι -> Type*} {α: Type*}

instance [∀i, Inv (A i)] : Inv (∀i, A i) where
  inv a i := (a i)⁻¹

instance [∀i, Neg (A i)] : Neg (∀i, A i) where
  neg a i := -a i

instance [∀i, Div (A i)] : Div (∀i, A i) where
  div a b i := a i / b i

instance [∀i, Sub (A i)] : Sub (∀i, A i) where
  sub a b i := a i - b i

instance [Inv α] : Inv (ι -> α) := inferInstance
instance [Neg α] : Neg (ι -> α) := inferInstance
instance [Div α] : Div (ι -> α) := inferInstance
instance [Sub α] : Sub (ι -> α) := inferInstance

@[simp] def Function.apply_inv [∀i, Inv (A i)] (a: ∀i, A i) (i: ι) : (a⁻¹: ∀i, A i) i = (a i)⁻¹ := rfl
@[simp] def Function.apply_neg [∀i, Neg (A i)] (a: ∀i, A i) (i: ι) : (-a: ∀i, A i) i = -a i := rfl
@[simp] def Function.apply_div [∀i, Div (A i)] (a b: ∀i, A i) (i: ι) : (a / b: ∀i, A i) i = a i / b i := rfl
@[simp] def Function.apply_sub [∀i, Sub (A i)] (a b: ∀i, A i) (i: ι) : (a - b: ∀i, A i) i = a i - b i := rfl

instance [∀i, Mul (A i)] [∀i, Inv (A i)] [∀i, One (A i)] [∀i, IsLawfulInvLeft (A i)] : IsLawfulInvLeft (∀i, A i) where
  inv_mul_cancel a := by ext i; apply inv_mul_cancel
instance [∀i, Mul (A i)] [∀i, Inv (A i)] [∀i, One (A i)] [∀i, IsLawfulInvRight (A i)] : IsLawfulInvRight (∀i, A i) where
  mul_inv_cancel a := by ext i; apply mul_inv_cancel
instance [∀i, Add (A i)] [∀i, Neg (A i)] [∀i, Zero (A i)] [∀i, IsLawfulNegLeft (A i)] : IsLawfulNegLeft (∀i, A i) where
  neg_add_cancel a := by ext i; apply neg_add_cancel
instance [∀i, Add (A i)] [∀i, Neg (A i)] [∀i, Zero (A i)] [∀i, IsLawfulNegRight (A i)] : IsLawfulNegRight (∀i, A i) where
  add_neg_cancel a := by ext i; apply add_neg_cancel

instance [∀i, Mul (A i)] [∀i, Inv (A i)] [∀i, Div (A i)] [∀i, IsLawfulDiv (A i)] : IsLawfulDiv (∀i, A i) where
  div_eq_mul_inv a b := by ext i; apply div_eq_mul_inv
instance [∀i, Add (A i)] [∀i, Neg (A i)] [∀i, Sub (A i)] [∀i, IsLawfulSub (A i)] : IsLawfulSub (∀i, A i) where
  sub_eq_add_neg a b := by ext i; apply sub_eq_add_neg

instance [∀i, GroupOps (A i)] [∀i, IsLawfulPowZ (A i)] : IsLawfulPowZ (∀i, A i) where
  zpow_ofNat a n := by ext i; apply zpow_ofNat
  zpow_negSucc a n := by ext i; apply zpow_negSucc
instance [∀i, AddGroupOps (A i)] [∀i, IsLawfulZSMul (A i)] : IsLawfulZSMul (∀i, A i) where
  ofNat_zsmul a n := by ext i; apply ofNat_zsmul
  negSucc_zsmul a n := by ext i; apply negSucc_zsmul

instance [∀i, GroupOps (A i)] [∀i, IsGroup (A i)] : IsGroup (∀i, A i) where
instance [∀i, AddGroupOps (A i)] [∀i, IsAddGroup (A i)] : IsAddGroup (∀i, A i) where

instance [Mul α] [Inv α] [One α] [IsLawfulInvLeft α] : IsLawfulInvLeft (ι -> α) := inferInstance
instance [Mul α] [Inv α] [One α] [IsLawfulInvRight α] : IsLawfulInvRight (ι -> α) := inferInstance
instance [Add α] [Neg α] [Zero α] [IsLawfulNegLeft α] : IsLawfulNegLeft (ι -> α) := inferInstance
instance [Add α] [Neg α] [Zero α] [IsLawfulNegRight α] : IsLawfulNegRight (ι -> α) := inferInstance

instance [Mul α] [Inv α] [Div α] [IsLawfulDiv α] : IsLawfulDiv (ι -> α) := inferInstance
instance [Add α] [Neg α] [Sub α] [IsLawfulSub α] : IsLawfulSub (ι -> α) := inferInstance

instance [GroupOps α] [IsLawfulPowZ α] : IsLawfulPowZ (ι -> α) := inferInstance
instance [AddGroupOps α] [IsLawfulZSMul α] : IsLawfulZSMul (ι -> α) := inferInstance

instance [GroupOps α] [IsGroup α] : IsGroup (ι -> α) := inferInstance
instance [AddGroupOps α] [IsAddGroup α] : IsAddGroup (ι -> α) := inferInstance
