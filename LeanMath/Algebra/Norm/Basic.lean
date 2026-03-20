import LeanMath.Algebra.Norm.Defs
import LeanMath.Algebra.Ring.Order
import LeanMath.Algebra.Group.Action.Defs
import LeanMath.Algebra.Module.Defs
import LeanMath.Order.Defs

section

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

@[simp]
def abs_one : ‖(1: γ)‖ = 1 := by
  have : ‖(1: γ)‖ = ‖(1: γ)‖ * ‖(1: γ)‖ := by
    rw (occs := [1]) [←one_mul 1]
    rw [norm_mul]
  rw (occs := [1]) [←mul_one (‖(1: γ)‖)] at this
  rw [Eq.comm, sub_eq_zero] at this
  rw [←mul_sub] at this
  rcases of_mul_eq_zero this with h | h
  have := subingleton_of_zero_eq_one _ (of_norm_eq_zero h).symm
  apply Subsingleton.allEq
  apply (sub_eq_zero _ _).mpr h

def abs_neg_one: ‖(-1: γ)‖ = 1 := by
  have : ‖(-1: γ)‖ * ‖(-1: γ)‖ = 1 := by
    rw [←norm_mul, ←neg_mul_left, ←neg_mul_right, neg_neg, one_mul, abs_one]
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

def abs_eq_max [Max γ] [IsSemiLatticeMax γ] [IsAbsMax γ] (a: γ) : ‖a‖ = a ⊔ -a := by
  rcases le_total a 0 with h | h
  rw [max_eq_right (le_neg_of_nonpos h)]
  rw [←neg_norm, abs_eq_of_nonneg]
  rw [←neg_zero]; apply neg_le_neg
  assumption
  rw [max_eq_left (neg_le_of_nonneg h)]
  apply abs_eq_of_nonneg
  assumption

def norm_pos {a: α} : 0 < ‖a‖ ↔ a ≠ 0 := by
  apply Iff.intro
  rintro h rfl
  rw [norm_zero] at h
  exact Relation.irrefl h
  intro h
  apply lt_of_le_of_ne
  apply norm_nonneg
  intro g
  have := of_norm_eq_zero g.symm
  contradiction

def norm_abs [Max γ] [IsSemiLatticeMax γ] [IsAbsMax γ] (a: α) : ‖‖a‖‖ = ‖a‖ := by
  rw [abs_eq_max]
  apply le_antisymm _ left_le_max
  apply max_le
  rfl
  apply neg_le_of_nonneg
  apply norm_nonneg

end

section

variable
  [Norm α γ] [Norm γ γ]
  [LE γ] [LT γ] [SMul γ α]
  [RingOps α] [IsRing α]
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
  [IsLawfulMulNorm α γ]

@[simp]
def norm_one [hα: Nontrivial α] : ‖(1: α)‖ = 1 := by
  have : ‖(1: α)‖ = ‖(1: α)‖ * ‖(1: α)‖ := by
    rw (occs := [1]) [←one_mul 1]
    rw [norm_mul]
  rw (occs := [1]) [←mul_one (‖(1: α)‖)] at this
  rw [Eq.comm, sub_eq_zero] at this
  rw [←mul_sub] at this
  rcases of_mul_eq_zero this with h | h
  have := subingleton_of_zero_eq_one _ (of_norm_eq_zero h).symm
  exfalso; have ⟨x, y, h⟩ := hα
  exact h (Subsingleton.allEq _ _)
  rw [←sub_eq_zero _ _] at h
  assumption

end
