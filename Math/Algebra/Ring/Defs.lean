module

public import Math.Algebra.AddGroupWithOne.Defs
public import Math.Algebra.Semiring.Defs

namespace Math

section Property

public class RingOps (α: Type*)
  extends AddGroupOps α, SemiringOps α, IntCast α where

public instance [AddGroupOps α] [MonoidOps α] [NatCast α] [IntCast α] : RingOps α where

public class IsNonUnitalNonAssocRing (α: Type*)
  [AddGroupOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsAddGroup α, IsLeftDistrib α, IsRightDistrib α, IsLawfulZeroMul α, IsAddComm α  where

public class IsNonUnitalRing (α: Type*)
  [AddGroupOps α] [Mul α] extends IsNonUnitalSemiring α, IsNonUnitalNonAssocRing α, IsSemigroup α where

public class IsNonAssocRing (α: Type*)
  [AddGroupOps α] [One α] [Mul α] [NatCast α] [IntCast α] extends IsNonAssocSemiring α, IsNonUnitalNonAssocRing α, IsAddGroupWithOne α, IsLawfulOne α where

public class IsRing (α: Type*) [RingOps α] : Prop extends IsSemiring α, IsNonUnitalRing α, IsNonAssocRing α, IsMonoidWithZero α where

end Property

section Basics

public instance : IsRing ℤ where
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

end Basics

section Theorems

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

public theorem intCast_add (n m: ℤ) : (n + m: ℤ) = (n: α) + m := by
  rw [←zsmul_one_eq_intCast, add_zsmul, zsmul_one_eq_intCast, zsmul_one_eq_intCast]

public theorem intCast_mul (n m: ℤ) : (n * m: ℤ) = (n: α) * m := by
  rw [←zsmul_one_eq_intCast, mul_zsmul, zsmul_eq_intCast_mul, zsmul_one_eq_intCast]

@[expose] public def RingHom.intCast : ℤ →+* α where
  toFun := Int.cast
  map_zero := intCast_zero
  map_one := intCast_one
  map_add := intCast_add
  map_mul := intCast_mul

@[simp] public theorem RingHom.apply_intCast (n: ℤ) : RingHom.intCast n = (n: α) := rfl

public instance : Subsingleton (ℤ →+* α) where
  allEq := by
    suffices ∀f: ℤ →+* α, f = RingHom.intCast by
      intro a b; rw [this a, this b]
    intro f; ext z
    show f (Int.cast z) = _
    rw [RingHom.apply_intCast, map_intCast]

public theorem intCast_pown (n: ℤ) (m: ℕ) : (n ^ m: ℤ) = (n: α) ^ m :=
  map_pown (f := RingHom.intCast) _ _

public theorem neg_sq (a: α) : (-a) ^ 2 = a ^ 2 := by
  rw [pown_two, pown_two, ←neg_mul_right, ←neg_mul_left, neg_neg]

public theorem sub_sq (a b: α) [IsCommAt a b] : (a - b) ^ 2 = a ^ 2 - (2: ℕ) * (a * b) + b ^ 2 := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_sq, ←neg_mul_right, ←neg_mul_right, neg_sq]

end Ring

end Theorems
