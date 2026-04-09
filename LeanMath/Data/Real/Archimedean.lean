import LeanMath.Data.Rational.Archimedean
import LeanMath.Data.Real.Char0Field

instance [LEM] : IsArchimedean ℝ := by
  apply archimedean_iff_rat_le.mpr
  intro r
  cases r using Real.cau_ind with | _ r =>
  have ⟨B, hB⟩ := r.bounded
  exists B
  apply CauchySeq.le_of_eventually_le
  exists 0; intro i hi
  apply le_trans
  show r i ≤ ‖r i‖
  rw [abs_eq_max]; apply left_le_max
  rw [←zero_add ‖r i‖]
  apply add_le_iff_le_sub.mpr
  have := hB i
  rw [←zero_add ‖r i‖] at this
  have := add_lt_iff_lt_sub.mp this
  apply le_of_lt; assumption
