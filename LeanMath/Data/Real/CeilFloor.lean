import LeanMath.Data.Real.Archimedean
import LeanMath.Order.ConditionallyCompleteLattice

namespace Real

variable [LEM]

noncomputable def floorSet (r: ℝ) : Set ℤ where
  Mem z := z ≤ r
noncomputable def ceilSet (r: ℝ) : Set ℤ where
  Mem z := r ≤ z

@[implicit_reducible]
def ceilSet_nonempty (r: ℝ) : (ceilSet r).Nonempty := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean ℝ) r
  exists x

@[implicit_reducible]
def ceilSet_bounded (r: ℝ) : (ceilSet r).BoundedBelow := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean ℝ) (-r)
  exists -x; intro y hy
  apply (intCast_le_intCast (α := ℝ) _ _).mp
  rw [intCast_neg]
  apply le_trans
  apply neg_le_neg
  assumption
  rw [neg_neg]; assumption

@[implicit_reducible]
def floorSet_nonempty : (floorSet r).Nonempty := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean ℝ) (-r)
  exists -x
  show -x ≤ r
  rw [←neg_neg r]; apply neg_le_neg
  assumption

@[implicit_reducible]
def floorSet_bounded : (floorSet r).BoundedAbove := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean ℝ) r
  exists x
  intro y hy
  apply (intCast_le_intCast (α := ℝ) _ _).mp
  apply le_trans _ hx
  assumption

noncomputable def floor (r: ℝ) : ℤ := sSup (floorSet r)
noncomputable def ceil (r: ℝ) : ℤ := sInf (ceilSet r)

def floor_le (r: ℝ) : r.floor ≤ r := by
  apply Int.csSup_mem (floorSet _)
  apply floorSet_nonempty
  apply floorSet_bounded

def le_ceil (r: ℝ) : r ≤ r.ceil := by
  apply Int.csInf_mem (ceilSet _)
  apply ceilSet_nonempty
  apply ceilSet_bounded

def floor_max (r: ℝ) : ∀x: ℤ, x ≤ r -> x ≤ r.floor := by
  intro x hx
  apply le_csSup
  apply floorSet_bounded
  assumption

def ceil_min (r: ℝ) : ∀x: ℤ, r ≤ x -> r.ceil ≤ x := by
  intro x hx
  apply csInf_le
  apply ceilSet_bounded
  assumption

def lt_floor_succ [LEM] (a r: ℝ) : a ≤ r -> a < r.floor + 1 := by
  intro h
  rw [←intCast_one, ←intCast_add, ←not_le]
  intro g
  have : r.floor + 1 ≤ r.floor := le_csSup (s := floorSet r) (a := r.floor + 1) floorSet_bounded ?_
  rw [←not_lt] at this; apply this
  exact Int.lt_succ r.floor
  exact le_trans g h

def ceil_pred_lt [LEM] (a r: ℝ) : r ≤ a -> r.ceil - 1 < a := by
  intro h
  rw [←intCast_one, ←intCast_sub, ←not_le]
  intro g
  have : r.ceil ≤ r.ceil - 1 := by
    apply csInf_le
    apply ceilSet_bounded
    exact le_trans h g
  rw [←not_lt] at this; apply this
  refine Int.sub_one_lt_of_le ?_; rfl

def exists_rat_between {a b: ℝ} : a < b ↔ ∃q: ℚ, a < q ∧ q < b := by
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
  have a_add_ninv_lt_b : a + (d: ℝ)⁻¹? < b := by
    rw [add_lt_iff_lt_sub, sub_eq_add_neg, add_comm,
      lt_add_iff_sub_lt, ←neg_lt_neg_iff, neg_neg, neg_sub]
    rw [←inv?_inv? (b - a)]
    apply inv?_lt_inv?
    apply pos_inv?; assumption
    assumption
  let n := (a * d).floor + 1
  let q : Rational := Rational.mk {
    num := n
    den := d
    den_ne_zero := d_ne_zero
  }
  have d_pos : 0 < (d: ℝ) := by
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
    apply le_refl
  · rw [ratCast_mk]; dsimp
    apply lt_of_le_of_lt _ a_add_ninv_lt_b
    unfold n
    rw [intCast_add, intCast_one, add_div?, one_div?]
    apply add_le_add_right
    apply le_of_mul_le_mul_of_pos_left
    exact d_pos; rw [mul_comm, div?_mul_cancel, mul_comm]
    apply floor_le

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
