import LeanMath.Algebra.AddGroupWithOne.Defs
import LeanMath.Data.ZMod.AddMonoidWithOne
import LeanMath.Data.ZMod.Group

instance : IsAddGroupWithOne (ZMod n) where
  intCast_ofNat _ := rfl
  intCast_negSucc _ := by
    apply ZMod.val_inj.mp; simp
    rw [Int.neg_emod_eq_sub_emod,
      Int.sub_emod, Int.emod_emod, ←Int.sub_emod,
      ←Int.neg_emod_eq_sub_emod]
    rfl
