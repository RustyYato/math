import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Dvd.Defs
import LeanMath.Data.Nat.Prime.Defs

namespace Int

def natCast_dvd_natCast' {a b: ℕ} : (a: ℤ) ∣ b ↔ a ∣ b := by
  apply Iff.intro
  · intro ⟨k, ha⟩
    cases k with
    | negSucc k =>
      rw [Int.ofNat_mul_negSucc] at ha
      match a with
      | a + 1 =>
        have := Int.natCast_nonneg b
        rw [ha] at this
        contradiction
      | 0 =>
        rw [zero_mul, natCast_zero, neg_zero] at ha
        cases Int.ofNat.inj ha
        apply Nat.dvd_refl
    | ofNat k =>
      rw [←natCast_mul] at ha
      cases Int.ofNat.inj ha
      apply Nat.dvd_mul_right
  · intro ⟨k, h⟩
    exists k
    rw [←natCast_mul]; congr

def minFact (z: ℤ) : ℕ := Nat.minFact z.natAbs

def minFact_dvd (z: ℤ) : (z.minFact: ℤ) ∣ z := by
  rw [←Int.dvd_natAbs, Int.natCast_dvd_natCast']
  apply Nat.minFact_dvd

def natCast_is_prime (n: ℕ) (hz: IsPrime n) : IsPrime (n: ℤ) where
  ne_zero h := hz.ne_zero (Int.ofNat.inj h)
  not_unit := by
    intro h
    rw [Int.is_unit_iff] at h
    rcases h with h | h
    cases Int.ofNat.inj h
    exact hz.not_unit inferInstance
    contradiction
  irreducible := by
    intro a b h
    have : n = Int.natAbs (a * b) := by rw [←h, Int.natAbs_natCast]
    rw [Int.natAbs_mul] at this
    iterate 2 rw [←Int.dvd_natAbs, Int.natCast_dvd_natCast']
    exact hz.irreducible this

def minFact_prime (z: ℤ) (hz: ¬IsUnit z) : IsPrime (z.minFact: ℤ) := by
  apply natCast_is_prime
  apply Nat.minFact_prime
  intro h
  rw [Int.natAbs_eq_iff] at h
  rcases h with rfl | rfl
  exact hz (by simp; infer_instance)
  exact hz (by simp; infer_instance)

#print axioms Int.natCast_dvd_natCast

def of_dvd_one (a: ℤ) : a ∣ 1 -> a = 1 ∨ a = -1 := by
  intro h
  rcases Int.le_total a 0 with g | g
  right
  have := Int.eq_one_of_dvd_one (Int.neg_le_neg g) (by rwa [Int.neg_dvd])
  rw [←this, neg_neg]
  left; apply Int.eq_one_of_dvd_one <;> assumption

def unit_of_dvd_one (a: ℤ) : a ∣ 1 -> IsUnit a := by
  rw [is_unit_iff]
  apply of_dvd_one

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

def gcd_eq_one_iff_no_common_prime_factors {a b: ℤ} : Int.gcd a b = 1 ↔ ∀k: ℤ, IsPrime k -> k ∣ a -> k ∣ b -> False := by
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
    apply Decidable.byContradiction
    intro h
    refine hk (Nat.minFact (a.gcd b)) (natCast_is_prime _ (Nat.minFact_prime _ h)) ?_ ?_
    apply Int.dvd_trans
    apply Int.natCast_dvd_natCast'.mpr
    apply Nat.minFact_dvd
    apply Int.gcd_dvd_left
    apply Int.dvd_trans
    apply Int.natCast_dvd_natCast'.mpr
    apply Nat.minFact_dvd
    apply Int.gcd_dvd_right

def prime_of_dvd_mul {p a b: ℤ} (ha: IsPrime p) : p ∣ a * b -> p ∣ a ∨ p ∣ b := by
  intro h
  sorry

def prime_dvd_pow (a b: ℤ) (n: ℕ) (ha: IsPrime a) : a ∣ b ^ n -> a ∣ b := by
  induction n with
  | zero =>
    simp; intro h
    nomatch ha.not_unit (unit_of_dvd_one _ h)
  | succ n ih =>
    rw [npow_succ]; intro h
    rcases prime_of_dvd_mul ha h with h | h
    · exact ih h
    · exact h

end Int
