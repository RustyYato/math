module

public import Math.Algebra.Module.Set.Basis.Defs
public import Math.Algebra.LinearCombo.Group

import Math.Algebra.Group.Defs.Lemmas
import Math.Algebra.Group.Defs.Hom

namespace Math.IsModule

variable {α: Type*} (R: Type*)
  [RingOps R] [IsRing R] [SMul R α]
  [AddGroupOps α] [IsAddGroup α] [IsAddComm α] [IsModule R α]

public theorem linindep_iff_eq_zero_of_eval_0 (U: Set α) : IsLinearIndependent R U ↔ ∀lc: LinearCombo U R, eval R U lc = 0 -> lc = 0 := by
  apply Iff.intro
  · intro lin lc h
    rw [←map_zero (eval R U)] at h
    exact lin h
  · intro h a b a_eq_b
    have : eval R U a - eval R U b = 0 := by rw [a_eq_b, sub_self]
    rw [←map_sub] at this
    rw [←zero_add b, ←h _ this, sub_eq_add_neg, add_assoc,
      neg_add_cancel, add_zero]
