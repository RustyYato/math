import LeanMath.Data.Poly.Defs
import LeanMath.Algebra.Ring.Action.Defs

namespace Poly

variable [RingOps P] [IsRing P]

instance : Neg P[X] where
  neg p := -1 • p

instance : Sub P[X] where
  sub a b := a + -b

instance : IntCast P[X] where
  intCast n := C n

instance : IsAddGroupWithOne P[X] where
  sub_eq_add_neg _ _ := rfl
  add_neg_cancel a := by
    show a + -1 • a = _
    induction a with
    | add a b iha ihb =>
      rw [smul_add, add_assoc, add_left_comm b, ←add_assoc,
        iha, ihb, add_zero]
    | term p n =>
      rw [smul_term, ←map_add,
        neg_one_zsmul, add_neg_cancel, map_zero]
  intCast_ofNat n := by
    show C ((n: ℤ): P) = (n: P[X])
    rw [intCast_ofNat]; rfl
  intCast_negSucc n := by
    show C (Int.negSucc n: P) = _
    rw [intCast_negSucc]
    rw [←neg_one_zsmul]
    show term _ _ = _
    rw [←smul_term]; rfl
  ofNat_zsmul a n := by ext i; apply ofNat_zsmul
  negSucc_zsmul a n := by
    ext i; apply Eq.trans; apply negSucc_zsmul
    simp; show _ = (-1 • (_: P[X])) i
    simp; rw [neg_one_zsmul]
instance [IsComm P] : IsRing P[X] where
instance : RingOps P[X] := inferInstance

end Poly
