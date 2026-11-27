module

public import Math.Algebra.AddMonoidWithOne.Defs.Basic
public import Math.Algebra.MonoidWithZero.Defs.Basic

import Math.Algebra.AddMonoidWithOne.Defs.Lemmas

namespace Math

section Property

public class IsLeftDistrib (α: Type*) [Add α] [Mul α] where
  mul_add (k a b: α) : k * (a + b) = k * a + k * b

public class IsRightDistrib (α: Type*) [Add α] [Mul α] where
  add_mul (a b k: α) : (a + b) * k = a * k + b * k

export IsLeftDistrib (mul_add)
export IsRightDistrib (add_mul)

public class SemiringOps (α: Type*)
  extends AddMonoidOps α, MonoidOps α, NatCast α where

public instance [AddMonoidOps α] [MonoidOps α] [NatCast α] : SemiringOps α where

public class IsNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] extends IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsLawfulZeroMul α, IsAddComm α  where

public class IsNonUnitalSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsSemigroup α where

public class IsNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [One α] [Mul α] [NatCast α] extends IsNonUnitalNonAssocSemiring α, IsAddMonoidWithOne α, IsLawfulOne α where

public class IsSemiring (α: Type*) [SemiringOps α] : Prop extends IsNonUnitalSemiring α, IsNonAssocSemiring α, IsMonoidWithZero α where

end Property

section Basics

public instance : IsSemiring ℕ where
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
public instance : IsSemiring ℤ where
  mul_add := Int.mul_add
  add_mul := Int.add_mul

end Basics

variable [SemiringOps α] [IsSemiring α]

public theorem nsmul_eq_natCast_mul (n: ℕ) (a: α) : n • a = n * a := by
  induction n with
  | zero => rw [natCast_zero, zero_mul, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, add_mul, one_mul, ih]

public theorem nsmul_eq_mul_natCast (n: ℕ) (a: α) : n • a = a * n := by
  induction n with
  | zero => rw [natCast_zero, mul_zero, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, mul_add, mul_one, ih]

public theorem natCast_mul (n m: ℕ) : (n * m: ℕ) = (n: α) * m := by
  rw [←nsmul_one_eq_natCast, mul_nsmul, nsmul_one_eq_natCast, nsmul_eq_natCast_mul]
