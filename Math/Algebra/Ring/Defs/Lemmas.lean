module

public import Math.Algebra.Semiring.Defs.Lemmas
public import Math.Algebra.AddGroupWithOne.Defs.Lemmas
public import Math.Algebra.Ring.Defs.Basic

namespace Math

section DistribAddGroup

variable [AddGroupOps α] [Mul α] [IsAddGroup α] [IsLawfulZeroMul α]

public theorem  neg_mul_left [IsRightDistrib α] (a b: α) : -(a * b) = -a * b := by
  symm; apply eq_neg_of_add
  rw [←add_mul, neg_add_cancel, zero_mul]
public theorem neg_mul_right [IsLeftDistrib α] (a b: α) : -(a * b) = a * -b := by
  symm; apply eq_neg_of_add
  rw [←mul_add, neg_add_cancel, mul_zero]

public instance [IsLeftDistrib α] [IsRightDistrib α] (a b: α) [IsCommAt a b] : IsCommAt a (-b) where
  mul_comm := by rw [←neg_mul_left, ←neg_mul_right, mul_comm]

end DistribAddGroup

section Ring

variable [RingOps α] [IsRing α]

public theorem zsmul_eq_intCast_mul (n: ℤ) (a: α) : n • a = n * a := by
  cases n with
  | ofNat n => dsimp; rw [intCast_ofNat, ofNat_zsmul, nsmul_eq_natCast_mul]
  | negSucc n => rw [intCast_negSucc, negSucc_zsmul, nsmul_eq_natCast_mul, neg_mul_left]

public theorem zsmul_eq_mul_intCast (n: ℤ) (a: α) : n • a = a * n := by
  cases n with
  | ofNat n => dsimp; rw [intCast_ofNat, ofNat_zsmul, nsmul_eq_mul_natCast]
  | negSucc n => rw [intCast_negSucc, negSucc_zsmul, nsmul_eq_mul_natCast, neg_mul_right]

public theorem intCast_mul (n m: ℤ) : (n * m: ℤ) = (n: α) * m := by
  rw [←zsmul_one_eq_intCast, mul_zsmul, zsmul_eq_intCast_mul, zsmul_one_eq_intCast]

public theorem neg_sq (a: α) : (-a) ^ 2 = a ^ 2 := by
  rw [pown_two, pown_two, ←neg_mul_right, ←neg_mul_left, neg_neg]

public theorem sub_sq (a b: α) [IsCommAt a b] : (a - b) ^ 2 = a ^ 2 - (2: ℕ) * (a * b) + b ^ 2 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_sq, ←neg_mul_right, ←neg_mul_right, neg_sq]

public theorem sub_mul (a b k: α) : (a - b) * k = a * k - b * k := by
  iterate 2 rw [sub_eq_add_neg]
  rw [add_mul, neg_mul_left]

public theorem mul_sub (a b k: α) : k * (a - b) = k * a - k * b := by
  iterate 2 rw [sub_eq_add_neg]
  rw [mul_add, neg_mul_right]

end Ring
