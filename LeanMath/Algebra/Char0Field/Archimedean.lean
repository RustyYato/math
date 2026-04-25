import LeanMath.Algebra.Char0Field.Defs
import LeanMath.Algebra.Field.Archimedean
import LeanMath.Data.Rational.Archimedean

variable [LEM] [FieldOps F] [RatCast F] [IsChar0Field F]
  [LT F] [LE F] [IsLinearOrder F]
  [IsOrderedSemiring F] [IsZeroLEOne F] [IsArchimedean F]

def exists_rat_between {a b: F} : a < b ↔ ∃q: ℚ, a < q ∧ q < b := by
  apply flip Iff.intro
  · intro ⟨q, ha, hb⟩
    exact lt_trans ha hb
  intro h
  have : 0 < b - a := by rwa [lt_sub_iff_add_lt, zero_add]
  have ⟨d, hn⟩ := archimedean_iff_nat_lt.mp inferInstance (b - a)⁻¹?

  have d_ne_zero : d ≠ 0 := by
    intro rfl
    rw [natCast_zero] at hn
    apply Relation.asymm hn
    apply pos_inv?
    assumption
  have a_add_ninv_lt_b : a + (d: F)⁻¹? < b := by
    rw [add_lt_iff_lt_sub, sub_eq_add_neg, add_comm,
      lt_add_iff_sub_lt, ←neg_lt_neg_iff, neg_neg, neg_sub]
    rw [←inv?_inv? (b - a)]
    apply inv?_lt_inv?
    apply pos_inv?; assumption
    assumption
  have := a * d
  let n := floor (a * d) + 1
  let q : Rational := Rational.mk {
    num := n
    den := d
    den_ne_zero := d_ne_zero
  }
  have d_pos : 0 < (d: F) := by
    match d with
    | _ + 1 => apply pos_natCast
    | 0 =>
      rw [natCast_zero] at hn
      exfalso; apply Relation.asymm hn
      apply pos_inv?; assumption
  exists q
  apply And.intro
  · rw [ratCast_mk]; dsimp
    apply lt_of_mul_lt_mul_of_pos_left
    exact d_pos
    rw (occs := [2]) [mul_comm]
    rw [div?_mul_cancel]
    rw [mul_comm]
    unfold n; rw [intCast_add, intCast_one]
    apply lt_floor_succ
  · rw [ratCast_mk]; dsimp
    apply lt_of_le_of_lt _ a_add_ninv_lt_b
    unfold n
    rw [intCast_add, intCast_one, add_div?, one_div?]
    apply add_le_add_right
    apply le_of_mul_le_mul_of_pos_left
    exact d_pos; rw [mul_comm, div?_mul_cancel, mul_comm]
    apply floor_le
