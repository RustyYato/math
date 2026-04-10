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

end Real
