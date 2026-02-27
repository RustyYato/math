import LeanMath.Algebra.AddMonoidWithOne.Defs
import LeanMath.Data.ZMod.Monoid

instance : IsAddMonoidWithOne (ZMod n) where
  natCast_zero := rfl
  natCast_one := by apply ZMod.val_inj.mp; simp
  natCast_succ x := by apply ZMod.val_inj.mp; simp
