import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Dvd.Defs
import LeanMath.Data.ZMod.Ring
import LeanMath.Data.Nat.Prime.Defs
import LeanMath.Data.Int.Prime

variable (p: ℕ) [IsPrime p]

namespace ZMod

instance : CheckedInv? (ZMod p) where
  checked_inv a _ := Int.gcdA a.val p

instance : CheckedDiv? (ZMod p) where
  checked_div a b _ := a * b⁻¹?

instance : CheckedZPow? (ZMod p) := defaultPowZ?

@[simp] def inv?_val (a: ZMod p) (ha: a ≠ 0) : a⁻¹? = Int.gcdA a.val p := rfl

end ZMod

instance : IsGroupWithZero (ZMod p) where
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl
  zero_ne_one := by
    intro h
    have := ZMod.val_inj.mpr h
    simp at this
    rw [Int.one_emod, if_neg] at this
    contradiction
    dsimp; intro rfl
    contradiction
  mul_inv?_cancel := by
    intro a h
    ext; dsimp
    rw [Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
    have := Int.bezout a.val p
    rw [Int.gcd_eq_one_iff_no_common_prime_factors.mpr] at this
    rw [←Int.add_mul_emod_self_left]
    rw [←this, ZMod.one_val]; rfl
    intro k k_prime k_dvd_a k_dvd_p
    rw [←Int.natAbs_dvd, Int.natCast_dvd_natCast'] at k_dvd_p
    suffices k.natAbs = p by
      rw [←Int.natAbs_dvd, this] at k_dvd_a
      have h₀ : 0 ≤ a.val := by
        rw [←a.mod_eq_self]; apply Int.emod_nonneg
        intro h
        cases h; contradiction
      have h₁ : a.val < p := by
        rw [←a.mod_eq_self]; apply Int.emod_lt
        intro h
        cases h; contradiction
      match h₂:a.val with
      | (x: ℕ) =>
        replace h₂ : a.val = x := h₂
        rw [h₂] at h₁ k_dvd_a
        rw [Int.natCast_dvd_natCast'] at k_dvd_a
        rw [Int.ofNat_lt] at h₁
        refine Nat.not_le_of_lt h₁ (Nat.le_of_dvd ?_ k_dvd_a)
        apply Nat.pos_of_ne_zero
        intro rfl
        apply h; ext; assumption
      | .negSucc x => rw [h₂] at h₀; contradiction
    rcases Nat.prime_def inferInstance _ k_dvd_p with h | h
    assumption
    have : IsPrime k.natAbs := ?_
    rw [h] at this; contradiction
    clear h
    infer_instance

instance : IsField (ZMod p) where
