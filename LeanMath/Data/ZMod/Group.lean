import LeanMath.Algebra.Group.Defs
import LeanMath.Data.ZMod.Monoid

instance : IsAddGroup (ZMod n) where
  add_neg_cancel a := by
    apply ZMod.val_inj.mp
    simp
    rw [add_neg_cancel, Int.zero_emod]
  sub_eq_add_neg a b := by
    apply ZMod.val_inj.mp
    simp
    rw [sub_eq_add_neg]
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul a b := by
    apply ZMod.val_inj.mp
    dsimp
    show (Int.negSucc b • _) % (n: ℤ) = _
    rw [negSucc_zsmul]
    rw [Int.neg_emod_eq_sub_emod, Int.sub_emod, Int.emod_self, Int.zero_sub]
    rfl
