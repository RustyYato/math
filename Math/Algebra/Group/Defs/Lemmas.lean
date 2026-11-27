module

public import Math.Algebra.Group.Defs.Basic
public import Math.Algebra.Monoid.Defs.Lemmas
import Math.Algebra.Group.Defs.Hom

namespace Math

public instance [Zero α] [Neg α] [Add α] [IsLawfulZero α] [IsAddSemigroup α] [IsLawfulNegLeft α] : IsLawfulNegZero α where
  neg_zero := by
    apply neg_eq_of_add
    rw [add_zero]

public instance [GroupOps α] [IsGroup α] : IsLawfulOneInv α where
  one_inv := by
    apply inv_eq_of_mul
    rw [one_mul]
public instance [AddGroupOps α] [IsAddGroup α] : IsLawfulNegZero α where
  neg_zero := one_inv (α := MulOfAdd α)

public theorem zero_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) : (0: ℤ) • a = 0 := by
  rw [show (0: ℤ) • a = (0: ℕ) • a from ofNat_zsmul _ _, zero_nsmul]
public theorem powz_zero [GroupOps α] [IsGroup α] (a: α) : a ^ (0: ℤ) = 1 :=
  zero_zsmul (α := AddOfMul α) a

public theorem one_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) : (1: ℤ) • a = a := by
  rw [show (1: ℤ) • a = (1: ℕ) • a from ofNat_zsmul _ _, one_nsmul]
public theorem powz_one [GroupOps α] [IsGroup α] (a: α) : a ^ (1: ℤ) = a :=
  one_zsmul (α := AddOfMul α) a

public theorem two_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) : (2: ℤ) • a = a + a := by
  rw [show (2: ℤ) • a = (2: ℕ) • a from ofNat_zsmul _ _, two_nsmul]
public theorem powz_two [GroupOps α] [IsGroup α] (a: α) : a ^ (2: ℤ) = a * a :=
  two_zsmul (α := AddOfMul α) a

public theorem zsmul_zero [AddGroupOps α] [IsAddGroup α] (n: ℤ) : n • (0: α) = 0 := by
  cases n; dsimp
  rw [ofNat_zsmul, nsmul_zero]
  rw [negSucc_zsmul, nsmul_zero, neg_zero]
public theorem one_powz [GroupOps α] [IsGroup α] (n: ℤ) : (1: α) ^ n = 1 := zsmul_zero (α := AddOfMul α) _

public theorem sub_zero [AddGroupOps α] [IsAddGroup α] (a: α) : a - 0 = a := by
  rw [sub_eq_add_neg, neg_zero ,add_zero]
public theorem div_one [GroupOps α] [IsGroup α] (a: α) : a / 1 = a :=
  sub_zero (α := AddOfMul α) _

public theorem neg_add_neg_rev [AddGroupOps α] [IsAddGroup α] (a b: α) : -a + -b = -(b + a) := by
  apply eq_neg_of_add
  rw [add_assoc, ←add_assoc (-b), neg_add_cancel, zero_add, neg_add_cancel]
public theorem neg_add_neg [AddGroupOps α] [IsAddGroup α] (a b: α) [IsAddCommAt a b] : -a + -b = -(a + b) := by
  rw [neg_add_neg_rev, add_comm]
public theorem inv_mul_inv_rev [GroupOps α] [IsGroup α] (a b: α) : a⁻¹ * b⁻¹ = (b * a)⁻¹ :=
  neg_add_neg_rev (α := AddOfMul α) _ _
public theorem inv_mul_inv [GroupOps α] [IsGroup α] (a b: α) [IsCommAt a b] : a⁻¹ * b⁻¹ = (a * b)⁻¹ :=
  neg_add_neg (α := AddOfMul α) (AddOfMul.mk a) (AddOfMul.mk b)

public theorem neg_neg [AddGroupOps α] [IsAddGroup α] (a: α) : - -a = a := by
  apply neg_eq_of_add
  rw [neg_add_cancel]
public theorem inv_inv [GroupOps α] [IsGroup α] (a: α) : a⁻¹⁻¹ = a :=
  neg_neg (α := AddOfMul α) _

public theorem neg_sub [AddGroupOps α] [IsAddGroup α] (a b: α) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ←neg_add_neg_rev, neg_neg]
public theorem div_inv [GroupOps α] [IsGroup α] (a b: α) : (a / b)⁻¹ = b / a :=
  neg_sub (α := AddOfMul α) _ _

public theorem zero_sub [AddGroupOps α] [IsAddGroup α] (a: α) : 0 - a = -a := by rw [sub_eq_add_neg, zero_add]
public theorem one_div [GroupOps α] [IsGroup α] (a: α) : 1 / a = a⁻¹ := by rw [div_eq_mul_inv, one_mul]

public theorem add_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) (n m: ℤ) : (n + m) • a = n • a + m • a := by
  change zsmul_hom a (n + m) = _; rw [map_add]; rfl
public theorem powz_add [GroupOps α] [IsGroup α] (a: α) (n m: ℤ) : a ^ (n + m) = a ^ n * a ^ m :=
  add_zsmul (α := AddOfMul α) a n m

public theorem mul_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) (n m: ℤ) : (n * m) • a = n • m • a := by
  rw [←smul_eq_mul n m]
  show zsmul_hom a (n • m) = n • zsmul_hom a m
  rw [map_zsmul]

public theorem powz_mul [GroupOps α] [IsGroup α] (a: α) (n m: ℤ) : a ^ (n * m) = (a ^ m) ^ n :=
  mul_zsmul (α := AddOfMul α) a n m

public theorem zsmul_add [AddGroupOps α] [IsAddGroup α] (a b: α) [IsAddCommAt a b] (n: ℤ) : n • (a + b) = n • a + n • b := by
  cases n; dsimp
  iterate 3 rw [ofNat_zsmul]
  rw [nsmul_add]
  iterate 3 rw [negSucc_zsmul]
  rw [nsmul_add, neg_add_neg]
public theorem mul_powz [GroupOps α] [IsGroup α] (a b: α) [IsCommAt a b] (n: ℤ) : (a * b) ^ n = a ^ n * b ^ n :=
  zsmul_add (α := AddOfMul α) (AddOfMul.mk a) (AddOfMul.mk b) n

public theorem neg_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) (n: ℤ) : (-n: ℤ) • a = -(n • a) := by
  apply eq_neg_of_add
  rw [←add_zsmul, neg_add_cancel, zero_zsmul]
public theorem powz_neg [GroupOps α] [IsGroup α] (a: α) (n: ℤ) : a ^ (-n: ℤ) = (a ^ n)⁻¹ :=
  neg_zsmul (α := AddOfMul α) _ _

public theorem neg_one_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) : (-1: ℤ) • a = -a := by
  rw [neg_zsmul, one_zsmul]
public theorem powz_neg_one [GroupOps α] [IsGroup α] (a: α) : a ^ (-1: ℤ) = a⁻¹ :=
  neg_one_zsmul (α := AddOfMul α) _

public theorem zsmul_neg [AddGroupOps α] [IsAddGroup α] (a: α) (n: ℤ) : n • (-a) = -(n • a) := by
  apply eq_neg_of_add
  rw [←zsmul_add, neg_add_cancel, zsmul_zero]
public theorem inv_powz [GroupOps α] [IsGroup α] (a: α) (n: ℤ) : (a⁻¹) ^ n = (a ^ n)⁻¹ :=
  zsmul_neg (α := AddOfMul α) _ _

public theorem sub_self [AddGroupOps α] [IsAddGroup α] (a: α) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]
public theorem div_self [GroupOps α] [IsGroup α] (a: α) : a / a = 1 :=
  sub_self (α := AddOfMul α) _

public theorem add_sub_assoc [AddGroupOps α] [IsAddGroup α] (a b c: α) : a + b - c = a + (b - c) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_assoc]
public theorem mul_div_assoc [GroupOps α] [IsGroup α] (a b c: α) : a * b / c = a * (b / c) :=
  add_sub_assoc (α := AddOfMul α) _ _ _

public theorem sub_add_cancel [AddGroupOps α] [IsAddGroup α] (a b: α) : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
public theorem div_mul_cancel [GroupOps α] [IsGroup α] (a b: α) : a / b * b = a :=
  sub_add_cancel (α := AddOfMul α) _ _
