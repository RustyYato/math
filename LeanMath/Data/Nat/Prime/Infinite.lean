import LeanMath.Data.Nat.Prime.Defs

namespace Nat

def fact : ℕ -> ℕ
| 0 => 1
| n + 1 => (n + 1) * fact n

def fact_ne_zero (n: ℕ) : fact n ≠ 0 := by
  induction n with
  | zero => nofun
  | succ n ih =>
    intro h
    rcases Nat.mul_eq_zero.mp h with h | h
    contradiction
    contradiction

def dvd_fact_of_le {n m: ℕ} : 0 < m -> m ≤ n -> m ∣ fact n := by
  intro h
  match m with
  | m + 1 =>
  clear h
  induction n with
  | zero => nofun
  | succ n ih =>
    intro g
    rw [Nat.le_iff_lt_or_eq, Or.comm] at g
    rcases g with g | g
    rw [g]; apply Nat.dvd_mul_right
    apply Nat.dvd_trans
    apply ih
    apply Nat.le_of_lt_succ
    assumption
    apply Nat.dvd_mul_left

def prime_larger_than (n: ℕ) : ℕ := (fact n + 1).minFact

def prime_larger_spec (n: ℕ) : IsPrime (prime_larger_than n) := by
  apply Nat.minFact_prime
  intro h
  replace h := Nat.succ.inj h
  exact fact_ne_zero n h

def le_prime_larger_than (n: ℕ) : n < prime_larger_than n := by
  apply Decidable.byContradiction
  intro h; rw [Nat.not_lt] at h
  have h₀: n.prime_larger_than ∣ fact n := by
    apply dvd_fact_of_le
    apply Nat.pos_of_ne_zero
    apply IsPrime.ne_zero
    apply prime_larger_spec
    assumption
  have h₁: n.prime_larger_than ∣ fact n + 1 := Nat.minFact_dvd (n.fact + 1)
  have := Nat.dvd_sub h₁ h₀
  rw [Nat.add_sub_cancel_left] at this
  exact (prime_larger_spec n).not_unit ((Nat.dvd_one.mp this) ▸ inferInstance)

end Nat
