import LeanMath.Algebra.Archimedean.Field
import LeanMath.Algebra.Semifield.Order
import LeanMath.Algebra.Ring.Order
import LeanMath.Order.ConditionallyCompleteLattice

variable [LEM] [FieldOps F] [IsDivisionRing F]
  [LT F] [LE F] [IsOrderedSemiring F] [IsZeroLEOne F]
  [IsArchimedean F]

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

variable [IsLinearOrder F]

def lt_floor_succ (r: F) : r < floor r + 1 := by
  rw [←intCast_one, ←intCast_add, ←not_le]
  intro g
  have : floor r + 1 ≤ floor r := le_csSup (s := floorSet r) (a := floor r + 1) floorSet_bounded ?_
  rw [←not_lt] at this; apply this
  exact Int.lt_succ (floor r)
  assumption

def ceil_pred_lt (r: F) : ceil r - 1 < r := by
  rw [←intCast_one, ←intCast_sub, ←not_le]
  intro g
  have : ceil r ≤ ceil r - 1 := by
    apply csInf_le
    apply ceilSet_bounded
    assumption
  rw [←not_lt] at this; apply this
  refine Int.sub_one_lt_of_le ?_; rfl
