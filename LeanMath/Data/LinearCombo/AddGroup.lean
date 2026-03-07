import LeanMath.Data.LinearCombo.Defs
import LeanMath.Algebra.Group.Action.Defs

namespace LinearCombo

variable [AddGroupOps R] [IsAddGroup R] [IsAddComm R]

instance : Neg (LinearCombo R α) where
  neg a := (-1) • a

instance : Sub (LinearCombo R α) where
  sub a b := a + -b

def neg_eq_neg_one_smul (a: LinearCombo R α) : -a = -1 • a := rfl

instance : IsAddGroup (LinearCombo R α) where
  sub_eq_add_neg _ _ := rfl
  add_neg_cancel := by
    intro a
    show a + -1 • a = 0
    induction a with
    | zero => simp [smul_zero, add_zero]
    | ι a r => rw [smul_ι, ←map_add, neg_zsmul, one_smul, add_neg_cancel, map_zero]
    | add a b iha ihb =>
      rw [
        smul_add,
        show (a + b) + ((-1 • a) + (-1 • b)) = (a + -1 • a) + (b + -1 • b) by ac_rfl,
        iha, ihb, add_zero
      ]
  ofNat_zsmul a n := by
    induction a with
    | zero => rw [smul_zero, smul_zero]
    | add _ _ iha ihb => rw [smul_add, smul_add, iha, ihb]
    | ι a r => simp [ofNat_zsmul]
  negSucc_zsmul a n := by
    induction a with
    | zero => rw [smul_zero, smul_zero, neg_eq_neg_one_smul, smul_zero]
    | add _ _ iha ihb => rw [smul_add, smul_add,
      neg_eq_neg_one_smul (_ + _), smul_add]; congr 1
    | ι a r => simp [negSucc_zsmul, neg_eq_neg_one_smul, neg_one_zsmul]

end LinearCombo
