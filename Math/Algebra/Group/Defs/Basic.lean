module

public import Math.Algebra.Monoid.Defs.Basic

namespace Math

section Property

public class IsLawfulDiv (α: Type*) [Mul α] [Div α] [Inv α] where
  div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
public class IsLawfulSub (α: Type*) [Add α] [Sub α] [Neg α] where
  sub_eq_add_neg (a b: α) : a - b = a + -b

export IsLawfulDiv (div_eq_mul_inv)
export IsLawfulSub (sub_eq_add_neg)

public class IsLawfulPowZ (α: Type*) [Pow α ℕ] [Pow α ℤ] [Inv α] where
  powz_ofNat (a: α) (n: ℕ) : a ^ (n: ℤ) = a ^ n
  powz_negSucc (a: α) (n: ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹
public class IsLawfulZSMul (α: Type*) [SMul ℕ α] [SMul ℤ α] [Neg α] where
  ofNat_zsmul (a: α) (n: ℕ) : (n: ℤ) • a = n • a
  negSucc_zsmul (a: α) (n: ℕ) : (Int.negSucc n) • a = -((n + 1) • a)

export IsLawfulPowZ (powz_ofNat powz_negSucc)
export IsLawfulZSMul (ofNat_zsmul negSucc_zsmul)

public class IsLawfulInvRight (α: Type*) [Mul α] [Inv α] [One α] where
  mul_inv_cancel (a: α) : a * a⁻¹ = 1

public class IsLawfulInvLeft (α: Type*) [Mul α] [Inv α] [One α] where
  inv_mul_cancel (a: α) : a⁻¹ * a = 1

public class IsLawfulNegRight (α: Type*) [Add α] [Neg α] [Zero α] where
  add_neg_cancel (a: α) : a + -a = 0

public class IsLawfulNegLeft (α: Type*) [Add α] [Neg α] [Zero α] where
  neg_add_cancel (a: α) : -a + a = 0

export IsLawfulInvRight (mul_inv_cancel)
export IsLawfulInvLeft (inv_mul_cancel)
export IsLawfulNegRight (add_neg_cancel)
export IsLawfulNegLeft (neg_add_cancel)

public class GroupOps (α: Type*) extends MonoidOps α, Div α, Inv α where
  toPowZ: Pow α ℤ
public class AddGroupOps (α: Type*) extends AddMonoidOps α, Sub α, Neg α where
  toZSMul: SMul ℤ α

public instance [GroupOps α] : Pow α ℤ := GroupOps.toPowZ
public instance [AddGroupOps α] : SMul ℤ α := AddGroupOps.toZSMul

public instance [MonoidOps α] [Pow α ℤ] [Div α] [Inv α] : GroupOps α where
  toPowZ := inferInstance
public instance [AddMonoidOps α] [SMul ℤ α] [Sub α] [Neg α] : AddGroupOps α where
  toZSMul := inferInstance

public class IsGroup (α: Type*) [GroupOps α] : Prop extends IsMonoid α, IsLawfulDiv α, IsLawfulPowZ α, IsLawfulInvLeft α where
public class IsAddGroup (α: Type*) [AddGroupOps α] : Prop extends IsAddMonoid α, IsLawfulSub α, IsLawfulZSMul α, IsLawfulNegLeft α where

public class IsLawfulOneInv (α: Type*) [Inv α] [One α] : Prop where
  one_inv : (1: α)⁻¹ = 1

public class IsLawfulNegZero (α: Type*) [Neg α] [Zero α] : Prop where
  neg_zero : -(0: α) = 0

export IsLawfulOneInv (one_inv)
export IsLawfulNegZero (neg_zero)

end Property

section Basic

public instance [Mul α] [Inv α] [One α] [IsLawfulInvLeft α] : IsLawfulInvRight αᵐᵒᵖ where
  mul_inv_cancel := inv_mul_cancel (α := α)
public instance [Mul α] [Inv α] [One α] [IsLawfulInvRight α] : IsLawfulInvLeft αᵐᵒᵖ where
  inv_mul_cancel := mul_inv_cancel (α := α)

public instance [Add α] [Neg α] [Zero α] [IsLawfulNegLeft α] : IsLawfulNegRight αᵃᵒᵖ where
  add_neg_cancel := neg_add_cancel (α := α)
public instance [Add α] [Neg α] [Zero α] [IsLawfulNegRight α] : IsLawfulNegLeft αᵃᵒᵖ where
  neg_add_cancel := add_neg_cancel (α := α)

public instance [Inv α] [Pow α ℕ] [Pow α ℤ] [IsLawfulPowZ α] : IsLawfulPowZ αᵐᵒᵖ where
  powz_ofNat := powz_ofNat (α := α)
  powz_negSucc := powz_negSucc (α := α)
public instance [Neg α] [SMul ℕ α] [SMul ℤ α] [IsLawfulZSMul α] : IsLawfulZSMul αᵃᵒᵖ where
  ofNat_zsmul := ofNat_zsmul (α := α)
  negSucc_zsmul := negSucc_zsmul (α := α)


public instance [Mul α] [Inv α] : IsLawfulDiv αᵐᵒᵖ where
  div_eq_mul_inv _ _ := rfl
public instance [Add α] [Neg α] : IsLawfulSub αᵃᵒᵖ where
  sub_eq_add_neg _ _ := rfl

public instance [Mul α] [Inv α] [One α] [IsLawfulInvLeft α] : IsLawfulNegLeft (AddOfMul α) where
  neg_add_cancel := inv_mul_cancel (α := α)
public instance [Mul α] [Inv α] [One α] [IsLawfulInvRight α] : IsLawfulNegRight (AddOfMul α) where
  add_neg_cancel := mul_inv_cancel (α := α)

public instance [Add α] [Neg α] [Zero α] [IsLawfulNegLeft α] : IsLawfulInvLeft (MulOfAdd α) where
  inv_mul_cancel := neg_add_cancel (α := α)
public instance [Add α] [Neg α] [Zero α] [IsLawfulNegRight α] : IsLawfulInvRight (MulOfAdd α) where
  mul_inv_cancel := add_neg_cancel (α := α)

public instance [Mul α] [Inv α] [One α] [IsSemigroup α] [IsLawfulOne α] [IsLawfulInvLeft α] : IsLawfulInvRight α where
  mul_inv_cancel a := by
    rw (occs := [1]) [←one_mul a, ←inv_mul_cancel (a⁻¹)]
    rw [mul_assoc (a⁻¹⁻¹), inv_mul_cancel, mul_one, inv_mul_cancel]

public instance [Mul α] [Inv α] [One α] [IsSemigroup α] [IsLawfulOne α] [IsLawfulInvRight α] : IsLawfulInvLeft α where
  inv_mul_cancel := mul_inv_cancel (α := αᵐᵒᵖ)
public instance [Add α] [Neg α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α] [IsLawfulNegLeft α] : IsLawfulNegRight α where
  add_neg_cancel := mul_inv_cancel (α := MulOfAdd α)
public instance [Add α] [Neg α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α] [IsLawfulNegRight α] : IsLawfulNegLeft α where
  neg_add_cancel := add_neg_cancel (α := αᵃᵒᵖ)
public instance [Add α] [Neg α] [Zero α] [IsLawfulNegRight α] : IsLawfulInvRight (MulOfAdd α) where
  mul_inv_cancel := add_neg_cancel (α := α)

public instance [GroupOps α] [IsLawfulPowZ α] : IsLawfulZSMul (AddOfMul α) where
  ofNat_zsmul := powz_ofNat (α := α)
  negSucc_zsmul := powz_negSucc (α := α)
public instance [AddGroupOps α] [IsLawfulZSMul α] : IsLawfulPowZ (MulOfAdd α) where
  powz_ofNat := ofNat_zsmul (α := α)
  powz_negSucc := negSucc_zsmul (α := α)

public instance [Mul α] [Inv α] [Div α] [IsLawfulDiv α] : IsLawfulSub (AddOfMul α) where
  sub_eq_add_neg := div_eq_mul_inv (α := α)
public instance [Add α] [Neg α] [Sub α] [IsLawfulSub α] : IsLawfulDiv (MulOfAdd α) where
  div_eq_mul_inv := sub_eq_add_neg (α := α)

public instance [GroupOps α] [IsGroup α] : IsAddGroup (AddOfMul α) where
public instance [AddGroupOps α] [IsAddGroup α] : IsGroup (MulOfAdd α) where

public instance [GroupOps α] [IsGroup α] : IsGroup αᵐᵒᵖ where
public instance [AddGroupOps α] [IsAddGroup α] : IsAddGroup αᵃᵒᵖ where

public instance [AddGroupOps α] [IsAddGroup α] : IsRightAddCancel α where
  of_add_right {k a b} h := by rw [←add_zero a, ←add_zero b, ←add_neg_cancel k, ←add_assoc, ←add_assoc, h]
public instance [AddGroupOps α] [IsAddGroup α] : IsLeftAddCancel α where
  of_add_left := of_add_right (α := αᵃᵒᵖ)

public instance [GroupOps α] [IsGroup α] : IsRightCancel α where
  of_mul_right := of_add_right (α := AddOfMul α)
public instance [GroupOps α] [IsGroup α] : IsLeftCancel α where
  of_mul_left := of_mul_right (α := αᵐᵒᵖ)

public instance : IsAddGroup ℤ where
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  neg_add_cancel := Int.add_left_neg
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul b a := by
    show Int.negSucc a * b = -((a + 1: ℕ) * b)
    cases b; rw [Int.ofNat_eq_natCast]
    rw [Int.negSucc_mul_ofNat, Int.ofNat_mul_ofNat]
    rw [Int.negSucc_mul_negSucc, Int.ofNat_mul_ofNat, Int.ofNat_mul_negSucc, Int.neg_neg]

end Basic

section Theorems

public theorem eq_inv_of_mul [GroupOps α] [IsGroup α] (a b: α) (h: a * b = 1) : a = b⁻¹ := by
  rw [←one_mul b⁻¹, ←h, mul_assoc, mul_inv_cancel, mul_one]
public theorem inv_eq_of_mul [One α] [Inv α] [Mul α] [IsLawfulOne α] [IsSemigroup α] [IsLawfulInvLeft α] (a b: α) (h: a * b = 1) : a⁻¹ = b := by
  rw [←mul_one a⁻¹, ←h, ←mul_assoc, inv_mul_cancel, one_mul]

public theorem eq_neg_of_add [AddGroupOps α] [IsAddGroup α] (a b: α) (h: a + b = 0) : a = -b :=
  eq_inv_of_mul (α := MulOfAdd α) _ _ h
public theorem neg_eq_of_add [Zero α] [Neg α] [Add α] [IsLawfulZero α] [IsAddSemigroup α] [IsLawfulNegLeft α] (a b: α) (h: a + b = 0) : -a = b :=
  inv_eq_of_mul (α := MulOfAdd α) _ _ h

public instance [AddGroupOps α] [IsAddGroup α] (a b: α) [IsAddCommAt a b] : IsAddCommAt a (-b) where
  add_comm := by
    apply of_add_right
    rw [add_assoc, neg_add_cancel, add_zero, add_assoc, add_comm a b, ←add_assoc, neg_add_cancel, zero_add]

public instance [GroupOps α] [IsGroup α] (a b: α) [IsCommAt a b] : IsCommAt a (b⁻¹) where
  mul_comm := add_comm (AddOfMul.mk a) (-AddOfMul.mk b)

end Theorems
