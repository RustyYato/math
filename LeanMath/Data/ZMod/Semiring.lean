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

private def ZMod.equivFin' [hn: NeZero n] : Fin n ≃+* ZMod n where
  toFun x := {
    val := x.val
    mod_eq_self := by
      apply Int.emod_eq_of_lt
      apply Int.natCast_nonneg
      apply Int.ofNat_lt.mpr
      exact x.isLt
  }
  invFun x := {
    val := x.val.toNat
    isLt := by
      apply Int.ofNat_lt.mp
      rw [←x.mod_eq_self, Int.toNat_of_nonneg]
      apply Int.emod_lt
      apply NeZero.ne
      apply Int.emod_nonneg
      apply NeZero.ne
  }
  leftInv a := by
    dsimp; congr
    rw [Int.toNat_of_nonneg]
    rw [←a.mod_eq_self]
    apply Int.emod_nonneg
    apply NeZero.ne
  rightInv a := rfl
  map_zero := rfl
  map_one := by
    cases n; rfl
    rename_i n
    cases n; rfl
    rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def ZMod.equivFin [NeZero n] : ZMod n ≃+* Fin n :=
  ZMod.equivFin'.symm
