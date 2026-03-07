import LeanMath.Data.LinearCombo.Defs
import LeanMath.Data.DirectSum.AddGroup

namespace LinearCombo

variable [AddGroupOps R] [IsAddGroup R] [IsAddComm R]

instance : Neg (LinearCombo R α) where
  neg a := ⟨-a.toDirectSum⟩

instance : Sub (LinearCombo R α) where
  sub a b := ⟨a.toDirectSum + -b.toDirectSum⟩

def neg_eq_neg_one_smul (a: LinearCombo R α) : -a = -1 • a := rfl

instance : IsAddGroup (LinearCombo R α) where
  sub_eq_add_neg _ _ := rfl
  add_neg_cancel a := by
    show equivDirectSum.symm (equivDirectSum a + -equivDirectSum a) = _
    rw [add_neg_cancel]; rfl
  ofNat_zsmul a n := by
    show equivDirectSum.symm (_ • equivDirectSum a) = _
    rw [ofNat_zsmul]; rfl
  negSucc_zsmul a n := by
    show equivDirectSum.symm (_ • equivDirectSum a) = _
    rw [negSucc_zsmul]; rfl

end LinearCombo
