import LeanMath.Data.ZMod.Defs
import LeanMath.Order.Defs

namespace ZMod

instance : LE (ZMod n) where
  le a b := a.val ≤ b.val
instance : LT (ZMod n) where
  lt a b := a.val < b.val

def orderEmb : ZMod n ↪o ℤ where
  toFun := ZMod.val
  inj := by intro a b h; ext; assumption
  map_rel := Iff.rfl

instance (a b: ZMod n) : Decidable (a ≤ b) :=
  (inferInstance: Decidable (a.val ≤ b.val))
instance (a b: ZMod n) : Decidable (a < b) :=
  (inferInstance: Decidable (a.val < b.val))

instance : IsLawfulLT (ZMod n) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := ℤ)

instance : @Relation.IsTrans (ZMod n) (· ≤ ·) := orderEmb.liftTrans
instance : IsLETotal (ZMod n) := orderEmb.liftTotal

instance : @Relation.IsAntisymm (ZMod n) (· ≤ ·) (· = ·) where
  antisymm h g := inj orderEmb (le_antisymm h g)

instance : IsLinearOrder (ZMod n) where
  refl a := le_refl a.val

end ZMod
