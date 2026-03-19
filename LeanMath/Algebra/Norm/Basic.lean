import LeanMath.Algebra.Norm.Defs
import LeanMath.Algebra.Ring.Order
import LeanMath.Algebra.Group.Action.Defs
import LeanMath.Algebra.Module.Defs
import LeanMath.Order.Defs

variable
  [Norm α γ] [Norm γ γ]
  [LE γ] [LT γ] [SMul γ α]
  [AddGroupOps α] [IsAddGroup α]
  [RingOps γ] [IsRing γ]
  [IsLawfulAbs γ] [IsLawfulNorm α γ]
  [IsDistributiveAction γ α]
  [IsLeftDistribSMul γ α]
  [IsLawfulZeroSMul γ α]
  [IsLinearOrder γ]
  [NoZeroDivisors γ]
  [IsZeroLEOne γ]
  [IsZeroNeOne γ]
  [IsOrderedAddCommMonoid γ]

def abs_one : ‖(1: γ)‖ = 1 := by
  have : ‖(1: γ)‖ = ‖(1: γ)‖ * ‖(1: γ)‖ := by
    rw (occs := [1]) [←one_mul 1]
    rw [abs_mul]
  rw (occs := [1]) [←mul_one (‖(1: γ)‖)] at this
  rw [Eq.comm, sub_eq_zero] at this
  rw [←mul_sub] at this
  rcases of_mul_eq_zero this with h | h
  have := subingleton_of_zero_eq_one _ (of_norm_eq_zero h).symm
  apply Subsingleton.allEq
  apply (sub_eq_zero _ _).mpr h

def abs_neg_one: ‖(-1: γ)‖ = 1 := by
  have : ‖(-1: γ)‖ * ‖(-1: γ)‖ = 1 := by
    rw [←abs_mul, ←neg_mul_left, ←neg_mul_right, neg_neg, one_mul, abs_one]
  replace : (‖(-1: γ)‖ + 1) * (‖(-1: γ)‖ - 1) = 0 := by
    rw [mul_sub, add_mul, add_mul]
    simp [one_mul, mul_one, this]
    rw [add_sub_assoc, add_comm _ 1, sub_add,
      sub_self, zero_sub, add_neg_cancel]
  rcases of_mul_eq_zero this with h | h
  · replace h := eq_neg_of_add _ _ h
    have := (intCast_lt_intCast (α := γ) (-1) 0).mpr (by decide)
    rw [intCast_neg, intCast_one, intCast_zero, ←h] at this
    nomatch not_le_of_lt this (norm_nonneg _)
  · rwa [←sub_eq_zero] at h

def neg_norm (a: α): ‖-a‖ = ‖a‖ := by
  rw [←one_mul ‖a‖, ←neg_one_zsmul, ←one_smul (R := γ) (-1 • _),
    ←smul_comm, ←smul_assoc, neg_one_zsmul, norm_smul]
  congr
  apply abs_neg_one

def norm_sub (a b: α) : ‖a - b‖ = ‖b - a‖ := by
  rw [←neg_sub, neg_norm]
