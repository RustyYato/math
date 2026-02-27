import LeanMath.Algebra.Semigroup.Defs
import LeanMath.Data.ZMod.Defs

instance : IsAddSemigroup (ZMod n) where
  add_assoc a b c := by
    apply ZMod.val_inj.mp
    dsimp
    rw [Int.add_emod a.val, Int.add_emod _ c.val,
      ←Int.emod_emod c.val, Int.emod_emod, ←Int.add_emod]
    rw [Int.add_emod b.val, Int.add_emod a.val,
      ←Int.emod_emod a.val,
      Int.emod_emod (_ + _),
      ←Int.add_emod _ (b.val % n + _)]
    rw [Int.emod_emod, add_assoc]

instance : IsSemigroup (ZMod n) where
  mul_assoc a b c := by
    apply ZMod.val_inj.mp
    dsimp
    rw [Int.mul_emod a.val, Int.mul_emod _ c.val,
      ←Int.emod_emod c.val, Int.emod_emod, ←Int.mul_emod]
    rw [Int.mul_emod b.val, Int.mul_emod a.val,
      ←Int.emod_emod a.val,
      Int.emod_emod (_ * _),
      ←Int.mul_emod _ (b.val % n * _)]
    rw [Int.emod_emod, mul_assoc]

instance : IsAddComm (ZMod n) where
  add_comm a b := by
    apply ZMod.val_inj.mp
    dsimp; rw [add_comm]

instance : IsComm (ZMod n) where
  mul_comm a b := by
    apply ZMod.val_inj.mp
    dsimp; rw [mul_comm]
