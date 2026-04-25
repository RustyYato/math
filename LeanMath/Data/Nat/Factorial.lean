import LeanMath.Tactic.TypeStar
import LeanMath.Logic.Checked

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

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply fact_ne_zero)

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

def fact_mul_pow_le_fact (n m k: ℕ) (h: m ≤ n) (hk: k ≤ n - m + 1) : (n - m).fact * k ^ m ≤ n.fact := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    simp [Nat.pow_succ]
    cases n with
    | zero => contradiction
    | succ n =>
      apply flip Nat.le_trans
      apply Nat.mul_le_mul_left
      apply ih; apply Nat.le_of_succ_le_succ
      assumption
      simpa using hk
      rw [←Nat.mul_assoc, Nat.mul_comm (n + 1)]
      simp
      apply Nat.mul_le_mul_left
      apply Nat.le_trans
      apply hk
      simp

end Nat
