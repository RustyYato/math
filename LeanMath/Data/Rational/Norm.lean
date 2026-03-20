import LeanMath.Algebra.Norm.Defs
import LeanMath.Data.Rational.Order

namespace Rational

instance : Norm ℚ ℚ where
  norm a := a ⊔ -a

private protected def abs_mul (a b: ℚ) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  show (a * b) ⊔ _ = (a ⊔ _) * (b ⊔ _)
  by_cases ha:0 ≤ a <;> by_cases hb:0 ≤ b
  rw [max_eq_left (neg_le_of_nonneg ha), max_eq_left (neg_le_of_nonneg hb),
    max_eq_left]
  apply neg_le_of_nonneg
  · apply mul_nonneg
    assumption
    assumption
  rw [mul_comm a, mul_comm (_ ⊔ _)]
  iterate 2
    rw [max_eq_right, max_eq_right, max_eq_left]
    rw [neg_mul_left]
    apply neg_le_of_nonneg
    assumption
    apply le_neg_of_nonpos
    apply le_of_lt; apply not_le.mp
    assumption
    apply le_neg_of_nonpos
    apply mul_nonpos_of_nonpos_of_nonneg
    apply le_of_lt; apply not_le.mp
    assumption
    assumption
  · rw [max_eq_left, max_eq_right, max_eq_right,
      ←neg_mul_left, ←neg_mul_right, neg_neg]
    iterate 2
      apply le_neg_of_nonpos
      apply le_of_lt; apply not_le.mp
      assumption
    apply neg_le_of_nonneg
    rw [←neg_neg (a * b), neg_mul_left, neg_mul_right]
    apply mul_nonneg
    apply neg_le_neg (a := a) (b := 0)
    apply le_of_lt; apply not_le.mp
    assumption
    apply neg_le_neg (a := b) (b := 0)
    apply le_of_lt; apply not_le.mp
    assumption

private protected def abs_add_le_add_abs (a b: ℚ) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  show (a + b) ⊔ _ ≤ (a ⊔ _) + (b ⊔ _)
  rcases le_total 0 a with h | h
  · rw [max_eq_left (neg_le_of_nonneg h)]
    rcases le_total 0 b with g | g
    · rw [max_eq_left (neg_le_of_nonneg g), max_eq_left]
      apply neg_le_of_nonneg
      apply nonneg_add
      assumption
      assumption
    · rw [max_eq_right (le_neg_of_nonpos g)]
      apply max_le
      apply add_le_add_left
      apply le_neg_of_nonpos
      assumption
      rw [neg_add_rev, add_comm]
      apply add_le_add_right
      apply neg_le_of_nonneg
      assumption
  · rw [max_eq_right (le_neg_of_nonpos h)]
    rcases le_total 0 b with g | g
    · rw [max_eq_left (neg_le_of_nonneg g)]
      apply max_le
      apply add_le_add_right
      apply le_neg_of_nonpos
      assumption
      rw [neg_add_rev, add_comm]
      apply add_le_add_left
      apply neg_le_of_nonneg
      assumption
    · rw [max_eq_right (le_neg_of_nonpos g), max_eq_right, neg_add_rev, add_comm]
      apply le_neg_of_nonpos
      apply (neg_le_neg_iff (b := 0) (a := a + b)).mp
      rw [neg_add_rev]; apply nonneg_add
      apply neg_le_neg (a := b) (b := 0)
      assumption
      apply neg_le_neg (a := a) (b := 0)
      assumption
instance : IsLawfulAbs ℚ where
  abs_nonneg a := by
    show 0 ≤ _ ⊔ _
    by_cases ha:0 ≤ a
    apply le_trans ha
    apply left_le_max
    apply le_trans _ right_le_max
    apply neg_le_neg (b := 0) (a := a)
    apply le_of_lt
    apply not_le.mp
    assumption
  abs_mul := abs_mul
  abs_add_le_add_abs := abs_add_le_add_abs
  abs_eq_zero {a} := by
    apply Iff.intro
    intro h
    apply le_antisymm
    apply le_trans
    show a ≤ ‖a‖
    apply left_le_max
    rw [h]
    apply not_lt.mp
    intro g
    suffices  0 < ‖a‖ by
      rw [h] at this
      exact Relation.irrefl this
    apply lt_of_lt_of_le _ right_le_max
    apply neg_lt_neg (a := a) (b := 0)
    assumption
    intro rfl
    decide +kernel
instance : IsAbsMax ℚ where
  abs_eq_of_nonneg a ha := by
    show _ ⊔ _ = _
    rw [max_eq_left]
    apply neg_le_of_nonneg
    assumption

end Rational
