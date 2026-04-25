import LeanMath.Algebra.Char0Field.Defs
import LeanMath.Data.Rational.Archimedean
import LeanMath.Algebra.Semifield.Order
import LeanMath.Algebra.Group.Order
import LeanMath.Order.ConditionallyCompleteLattice

variable [LEM] [FieldOps F] [RatCast F] [IsChar0Field F]
  [LT F] [LE F] [IsLinearOrder F]
  [IsOrderedSemiring F] [IsZeroLEOne F] [IsArchimedean F]

noncomputable def floorSet (r: F) : Set ℤ where
  Mem z := z ≤ r
noncomputable def ceilSet (r: F) : Set ℤ where
  Mem z := r ≤ z

@[implicit_reducible]
def ceilSet_nonempty (r: F) : (ceilSet r).Nonempty := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean F) r
  exists x

@[implicit_reducible]
def ceilSet_bounded (r: F) : (ceilSet r).BoundedBelow := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean F) (-r)
  exists -x; intro y hy
  apply (intCast_le_intCast (α := F) _ _).mp
  rw [intCast_neg]
  apply le_trans
  apply neg_le_neg
  assumption
  rw [neg_neg]; assumption

@[implicit_reducible]
def floorSet_nonempty {r: F} : (floorSet r).Nonempty := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean F) (-r)
  exists -x
  show (-x: ℤ) ≤ r
  rw [←neg_neg r, intCast_neg]; apply neg_le_neg
  assumption

@[implicit_reducible]
def floorSet_bounded {r: F} : (floorSet r).BoundedAbove := by
  have ⟨x, hx⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean F) r
  exists x
  intro y hy
  apply (intCast_le_intCast (α := F) _ _).mp
  apply le_trans _ hx
  assumption

noncomputable def floor (r: F) : ℤ := sSup (floorSet r)
noncomputable def ceil (r: F) : ℤ := sInf (ceilSet r)

def floor_le (r: F) : floor r ≤ r := by
  apply Int.csSup_mem (floorSet _)
  apply floorSet_nonempty
  apply floorSet_bounded

def le_ceil (r: F) : r ≤ ceil r := by
  apply Int.csInf_mem (ceilSet _)
  apply ceilSet_nonempty
  apply ceilSet_bounded

def floor_max (r: F) : ∀x: ℤ, x ≤ r -> x ≤ floor r := by
  intro x hx
  apply le_csSup
  apply floorSet_bounded
  assumption

def ceil_min (r: F) : ∀x: ℤ, r ≤ x -> ceil r ≤ x := by
  intro x hx
  apply csInf_le
  apply ceilSet_bounded
  assumption

def lt_floor_succ (a r: F) : a ≤ r -> a < floor r + 1 := by
  intro h
  rw [←intCast_one, ←intCast_add, ←not_le]
  intro g
  have : floor r + 1 ≤ floor r := le_csSup (s := floorSet r) (a := floor r + 1) floorSet_bounded ?_
  rw [←not_lt] at this; apply this
  exact Int.lt_succ (floor r)
  exact le_trans g h

def ceil_pred_lt (a r: F) : r ≤ a -> ceil r - 1 < a := by
  intro h
  rw [←intCast_one, ←intCast_sub, ←not_le]
  intro g
  have : ceil r ≤ ceil r - 1 := by
    apply csInf_le
    apply ceilSet_bounded
    exact le_trans h g
  rw [←not_lt] at this; apply this
  refine Int.sub_one_lt_of_le ?_; rfl

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
    apply le_refl
  · rw [ratCast_mk]; dsimp
    apply lt_of_le_of_lt _ a_add_ninv_lt_b
    unfold n
    rw [intCast_add, intCast_one, add_div?, one_div?]
    apply add_le_add_right
    apply le_of_mul_le_mul_of_pos_left
    exact d_pos; rw [mul_comm, div?_mul_cancel, mul_comm]
    apply floor_le
