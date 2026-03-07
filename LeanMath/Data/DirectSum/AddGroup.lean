import LeanMath.Data.DirectSum.Defs
import LeanMath.Algebra.Group.Action.Defs

namespace DirectSum

variable {α: Type*} {R: α -> Type*}

variable [∀a, AddGroupOps (R a)] [∀a, IsAddGroup (R a)] [∀a, IsAddComm (R a)]

instance : Neg (⊕i, R i) where
  neg a := (-1) • a

instance : Sub (⊕i, R i) where
  sub a b := a + -b

def neg_eq_neg_one_zsmul (a: ⊕a, R a) : -a = -1 • a := rfl

instance : IsAddGroup (⊕i, R i) where
  sub_eq_add_neg _ _ := rfl
  add_neg_cancel a := by
    induction a with
    | zero => rw [neg_eq_neg_one_zsmul, smul_zero, add_zero]
    | add a b iha ihb =>
      rw [neg_eq_neg_one_zsmul, smul_add]
      simp [←neg_eq_neg_one_zsmul]
      rw [
        show ((a + b) + (-a + -b)) = ((a + -a) + (b + -b)) by ac_rfl,
        iha, ihb, add_zero
      ]
    | ι a r =>
      rw [neg_eq_neg_one_zsmul, smul_ι, ←map_add,
        neg_one_zsmul, add_neg_cancel, map_zero]
  ofNat_zsmul a n := by
    induction a with
    | zero => rw [smul_zero, smul_zero]
    | add a b iha ihb => rw [smul_add, smul_add, iha, ihb]
    | ι a r => rw [smul_ι, smul_ι, ofNat_zsmul]
  negSucc_zsmul a n := by
    induction a with
    | zero => rw [smul_zero, smul_zero, neg_eq_neg_one_zsmul, smul_zero]
    | add a b iha ihb => rw [smul_add, smul_add, iha, ihb,
      neg_eq_neg_one_zsmul, neg_eq_neg_one_zsmul,
      neg_eq_neg_one_zsmul, smul_add]
    | ι a r => rw [smul_ι, smul_ι, negSucc_zsmul,
      neg_eq_neg_one_zsmul, smul_ι, neg_one_zsmul]

end DirectSum
