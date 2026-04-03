import LeanMath.Data.ZMod.Defs
import LeanMath.Order.Defs

namespace ZMod

instance : LE (ZMod n) where
  le a b := a.val ≤ b.val
instance : LT (ZMod n) where
  lt a b := a.val < b.val

instance (n: ℕ) [NeZero n] : NeZero (Nat.cast n: ℤ) where
  out h := NeZero.ne _ (Int.ofNat.inj h)

def orderEmb : ZMod n ↪o ℤ where
  toFun := ZMod.val
  inj := by intro a b h; ext; assumption
  map_rel := Iff.rfl

def embNat [NeZero n] : ZMod n ↪ ℕ where
  toFun x := x.val.toNat
  inj := by
    intro a b h; ext;
    dsimp at h
    replace h := congrArg (Nat.cast (R := ℤ)) h
    rwa [Int.ofNat_toNat, Int.ofNat_toNat, max_eq_left, max_eq_left] at h
    rw [←b.mod_eq_self]
    apply Int.emod_nonneg
    apply NeZero.ne
    rw [←a.mod_eq_self]
    apply Int.emod_nonneg
    apply NeZero.ne

def natCast_embNat [NeZero n] (a: ZMod n) : embNat a = a.val := by
  show (Int.toNat _: ℤ) = _
  rw [Int.ofNat_toNat, max_eq_left]
  rw [←a.mod_eq_self]
  apply Int.emod_nonneg
  apply NeZero.ne

def orderEmbNat [NeZero n] : ZMod n ↪o ℕ where
  toEmbedding := embNat
  map_rel {a b} := by
    show a ≤ b ↔ embNat a ≤ embNat b
    apply Iff.trans _ Int.ofNat_le
    rw [natCast_embNat, natCast_embNat]
    rfl

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

instance : IsLinearOrder (ZMod n) where
  refl a := le_refl a.val

instance [NeZero n] : @Relation.IsWelFounded (ZMod n) (· < ·) := (toLtHom orderEmbNat).liftWellfounded

end ZMod
