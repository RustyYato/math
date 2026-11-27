module

public import Math.Algebra.Monoid.Defs.Lemmas
public import Math.Algebra.AddMonoidWithOne.Defs.Basic

import Math.Algebra.Monoid.Defs.Hom

namespace Math

public theorem natCast_one [Add α] [Zero α] [One α] [NatCast α] [IsLawfulZero α] [IsLawfulNatCast α] : (1: ℕ) = (1: α) := by
  rw [natCast_succ, natCast_zero, zero_add]

variable [AddMonoidOps α] [One α] [NatCast α] [IsAddMonoidWithOne α]

public theorem nsmul_one_eq_natCast (n: ℕ) : n • (1: α) = n := by
  induction n with
  | zero => rw [zero_nsmul, natCast_zero]
  | succ n ih => rw [succ_nsmul, natCast_succ, ih]

public theorem natCast_add (n m: ℕ) : (n + m: ℕ) = (n + m: α) := by
  rw [←nsmul_one_eq_natCast, add_nsmul, nsmul_one_eq_natCast, nsmul_one_eq_natCast]
