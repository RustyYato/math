module

public import Math.Algebra.Monoid.Defs

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

public instance [Zero α] [Neg α] [Add α] [IsLawfulZero α] [IsAddSemigroup α] [IsLawfulNegLeft α] : IsLawfulNegZero α where
  neg_zero := by
    apply neg_eq_of_add
    rw [add_zero]

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
public theorem inv_mul_inv_neg_rev [GroupOps α] [IsGroup α] (a b: α) : a⁻¹ * b⁻¹ = (b * a)⁻¹ :=
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

public theorem sub_nsmul [AddGroupOps α] [IsAddGroup α] (a: α) (n m: ℕ) (h: m ≤ n) : (n - m) • a = n • a - m • a := by
  induction m generalizing n with
  | zero => rw [Nat.sub_zero, zero_nsmul, sub_zero]
  | succ m ih =>
    cases n with
    | zero => nomatch h
    | succ n =>
      replace h := Nat.le_of_succ_le_succ h
      rw [Nat.succ_sub_succ, ih _ h, succ_nsmul, succ_nsmul_left, sub_eq_add_neg,
        sub_eq_add_neg, ←neg_add_neg a (m • a), ←add_assoc,
        add_assoc _ a, add_neg_cancel, add_zero]
public theorem pown_sub [GroupOps α] [IsGroup α] (a: α) (n m: ℕ) (h: m ≤ n) : a ^ (n - m) = a ^ n / a ^ m :=
  sub_nsmul (α := AddOfMul α) _ _ _ h

theorem subNatNat_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) (n m: ℕ) : (Int.subNatNat n m) • a = n • a - m • a := by
  unfold Int.subNatNat
  split <;> rename_i k h; clear k; dsimp
  · rw [ofNat_zsmul, sub_nsmul]
    exact Nat.le_of_sub_eq_zero h
  · rw [negSucc_zsmul, ←show m - n = k + 1 from h]
    rw [sub_nsmul, sub_eq_add_neg, ←neg_add_neg_rev, neg_neg, sub_eq_add_neg]
    apply Nat.le_of_lt
    apply Nat.lt_of_sub_pos
    rw [h]; apply Nat.zero_lt_succ

public theorem add_zsmul [AddGroupOps α] [IsAddGroup α] (a: α) (n m: ℤ) : (n + m) • a = n • a + m • a := by
  rcases n with n | n <;> rcases m with m | m
  any_goals dsimp
  · rw [Int.ofNat_add_ofNat]
    iterate 3 rw [ofNat_zsmul]
    rw [add_nsmul]
  · rw [Int.ofNat_add_negSucc, subNatNat_zsmul, negSucc_zsmul, ofNat_zsmul, sub_eq_add_neg]
  · rw [Int.negSucc_add_ofNat, subNatNat_zsmul, negSucc_zsmul, ofNat_zsmul, add_comm, sub_eq_add_neg]
  · rw [Int.negSucc_add_negSucc]
    iterate 3 rw [negSucc_zsmul]
    rw [neg_add_neg, ←add_nsmul]; congr 2
    rw [←Nat.succ_add]; rfl
public theorem powz_add [GroupOps α] [IsGroup α] (a: α) (n m: ℤ) : a ^ (n + m) = a ^ n * a ^ m :=
  add_zsmul (α := AddOfMul α) a n m

@[expose] public def zsmul_hom [AddGroupOps α] [IsAddGroup α] (a: α) : ℤ →+ α where
  toFun n := n • a
  map_zero := by rw [zero_zsmul]
  map_add n m := by rw [add_zsmul]

@[expose] public def powz_hom [GroupOps α] [IsGroup α] (a: α) : ℤ →ₘ+ α where
  toFun n := a ^ n
  map_zero_to_one := map_zero (β := AddOfMul α) (zsmul_hom (AddOfMul.mk a))
  map_add_to_mul := map_add (β := AddOfMul α) (zsmul_hom (AddOfMul.mk a))

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

public def AddGroupEquiv.conj [AddGroupOps α] [IsAddGroup α] (x: α) : α ≃+ α where
  toFun a := x + a + -x
  invFun a := -x + a + x
  leftInv a := by dsimp; rw [←add_assoc x, ←add_assoc x, add_neg_cancel, zero_add, add_assoc, add_neg_cancel, add_zero]
  rightInv a := by dsimp; rw [←add_assoc (-x), ←add_assoc (-x), neg_add_cancel, zero_add, add_assoc, neg_add_cancel, add_zero]
  map_zero := by rw [add_zero, add_neg_cancel]
  map_add a b := by
    rw [add_assoc x a, add_assoc x (_ + -x), add_assoc a (-x),
      ←add_assoc (-x), ←add_assoc (-x), neg_add_cancel, zero_add]
    repeat rw [add_assoc]

public def GroupEquiv.conj [GroupOps α] [IsGroup α] (x: α) : α ≃* α where
  toFun a := x * a * x⁻¹
  invFun a := x⁻¹ * a * x
  leftInv := (AddGroupEquiv.conj (AddOfMul.mk x)).leftInv
  rightInv := (AddGroupEquiv.conj (AddOfMul.mk x)).rightInv
  map_one := (AddGroupEquiv.conj (AddOfMul.mk x)).map_zero
  map_mul := (AddGroupEquiv.conj (AddOfMul.mk x)).map_add

@[simp] theorem AddGroupEquiv.apply_conj [AddGroupOps α] [IsAddGroup α] (x a: α) : AddGroupEquiv.conj x a = x + a + -x := rfl
@[simp] theorem AddGroupEquiv.apply_symm_conj [AddGroupOps α] [IsAddGroup α] (x a: α) : (AddGroupEquiv.conj x).symm a = -x + a + x := rfl
@[simp] theorem AddGroupEquiv.conj_symm [AddGroupOps α] [IsAddGroup α] (x: α) : (AddGroupEquiv.conj x).symm = AddGroupEquiv.conj (-x) := by
  ext i; dsimp; rw [neg_neg]

@[simp] theorem GroupEquiv.apply_conj [GroupOps α] [IsGroup α] (x a: α) : GroupEquiv.conj x a = x * a * x⁻¹ := rfl
@[simp] theorem GroupEquiv.apply_symm_conj [GroupOps α] [IsGroup α] (x a: α) : (GroupEquiv.conj x).symm a = x⁻¹ * a * x := rfl
@[simp] theorem GroupEquiv.conj_symm [GroupOps α] [IsGroup α] (x: α) : (GroupEquiv.conj x).symm = GroupEquiv.conj (x⁻¹) := by
  ext i; dsimp; rw [inv_inv]

end Theorems

namespace OfEquiv

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

end OfEquiv
