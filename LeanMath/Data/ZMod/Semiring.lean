import LeanMath.Algebra.Semiring.Defs
import LeanMath.Data.ZMod.AddMonoidWithOne

instance : IsLeftDistrib (ZMod n) where
  mul_add k a b := by
    apply ZMod.val_inj.mp; dsimp
    simp
    rw [Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
    rw [mul_add]
instance : IsRightDistrib (ZMod n) := inferInstance
instance : IsSemiring (ZMod n) where
