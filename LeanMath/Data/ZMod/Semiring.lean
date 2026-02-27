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

def ZMod.equivInt : ZMod 0 ≃+* Int where
  toFun x := x.val
  invFun x := {
    val := x
    mod_eq_self := Int.emod_zero _
  }
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := Int.emod_zero _
  map_mul _ _ := Int.emod_zero _
