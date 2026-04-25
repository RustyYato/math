import LeanMath.Data.Real.Archimedean
import LeanMath.Algebra.Char0Field.Archimedean

namespace Real

variable [LEM]

noncomputable abbrev floor (r: ℝ) : ℤ := _root_.floor r
noncomputable abbrev ceil (r: ℝ) : ℤ := _root_.ceil r

def of_norm_lt_all_pos_rat (a: ℝ) : (∀ε: ℚ, 0 < ε -> ‖a‖ < ε) -> a = 0 := by
  intro ha
  rcases lt_trichotomy a 0 with h | h | h
  · have ⟨q, a_lt_q, q_neg⟩ := exists_rat_between.mp h
    have := ha (-q) (by
      rwa [←neg_zero, neg_lt_neg_iff, ←ratCast_lt_ratCast (α := ℝ),
        ratCast_zero])
    rw [←neg_norm, abs_eq_of_nonneg,
      ←apply_ratCastHom, map_neg, apply_ratCastHom,
      neg_lt_neg_iff] at this
    nomatch Relation.asymm a_lt_q this
    rw [←neg_zero, neg_le_neg_iff]; apply le_of_lt
    assumption
  · assumption
  · have ⟨q, q_pos, a_lt_q⟩ := exists_rat_between.mp h
    have := ha q (by
      rwa [←ratCast_lt_ratCast (α := ℝ), ratCast_zero])
    rw [abs_eq_of_nonneg] at this
    nomatch Relation.asymm a_lt_q this
    apply le_of_lt
    assumption

def eq_of_lim_eq_zero (a b: ℝ) : (∀ε: ℚ, 0 < ε -> ‖a - b‖ < ε) -> a = b := by
  intro h
  exact (sub_eq_zero _ _).mpr (of_norm_lt_all_pos_rat _ h)

end Real
