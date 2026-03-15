import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Dvd.Defs

namespace Int

def of_dvd_one (a: ℤ) : a ∣ 1 -> a = 1 ∨ a = -1 := by
  intro h
  rcases Int.le_total a 0 with g | g
  right
  have := Int.eq_one_of_dvd_one (Int.neg_le_neg g) (by rwa [Int.neg_dvd])
  rw [←this, neg_neg]
  left; apply Int.eq_one_of_dvd_one <;> assumption

def of_eq_one {a b: ℤ} : a * b = 1 -> a = 1 ∧ b = 1 ∨ a = -1 ∧ b = -1 := by
  intro h
  have htemp₀ (a k: ℕ) : (a + 2) * (k + 1) ≠ 1 := by
    rw [mul_add, add_mul, add_mul]
    simp only [←add_assoc]; intro h
    have : 2 ≤ 1 := by rw [←h]; apply Nat.le_add_left
    contradiction
  have htemp₁ (a k: ℕ) : -((a + 2) * k: ℕ) ≠ (1: ℤ) := by
    intro h
    have := Int.zero_lt_one
    rw [←h] at this
    exact Int.not_le.mpr this (Int.neg_natCast_le_ofNat _ _)
  match a with
  | 1 => rw [one_mul] at h; subst b; decide
  | -1 =>
    rw [Int.neg_one_mul] at h
    right; simp; rw [←h, neg_neg]
  | 0 => rw [zero_mul] at h; contradiction
  | (a + 2: ℕ) =>
    match b with
    | 0 => rw [mul_zero] at h; contradiction
    | (b + 1: ℕ) =>
      rw [←natCast_mul] at h
      have := Int.ofNat.inj h
      exfalso; apply htemp₀
      assumption
    | -(b + 1: ℕ) =>
      exfalso
      rw [←neg_mul_right, ←natCast_mul] at h
      apply htemp₁
      assumption
  | -(a + 2: ℕ) =>
    rw [←neg_mul_left] at h
    exfalso
    match b with
    | (b: ℕ) =>
      rw [←natCast_mul] at h
      apply htemp₁
      assumption
    | -(b + 1: ℕ) =>
      rw [neg_mul_right, neg_neg, ←natCast_mul] at h
      replace h := Int.ofNat.inj h
      apply htemp₀
      assumption

def gcd_eq_zero_iff_no_common_prime_factors {a b: ℤ} :
  Int.gcd a b = 1 ↔ ∀k: ℤ, IsPrime k -> k ∣ a -> k ∣ b -> False := by
  apply Iff.intro
  · intro h k kprime ka kb
    obtain ⟨a, rfl⟩ := ka
    obtain ⟨b, rfl⟩ := kb
    rw [Int.gcd_mul_left] at h
    have := Int.natAbs_eq_iff.mp (Nat.eq_one_of_mul_eq_one_right h)
    rcases this with rfl | rfl
    exact kprime.not_unit (by simp; infer_instance)
    exact kprime.not_unit (by simp; infer_instance)
  · intro hk
    sorry

end Int
