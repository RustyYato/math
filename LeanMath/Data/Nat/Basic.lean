import LeanMath.Tactic.TypeStar

namespace Nat

def mul_lt_mul_left' {a b c : ℕ} : 0 < a → (a * b < a * c ↔ b < c) := by
  intro h
  cases a; contradiction; clear h
  rename_i a
  induction b generalizing c with
  | zero => simp
  | succ b ih =>
    cases c with
    | zero => simp
    | succ c =>
    rw [mul_succ, mul_succ]
    rw [Nat.add_lt_add_iff_right, Nat.succ_lt_succ_iff]
    apply ih

def div_lt_of_lt_mul' {m n k : ℕ} : m < n * k → m / n < k := by
  intro h
  rw [←Nat.div_add_mod m n] at h
  replace h : n * (m / n) < n * k := by
    apply Nat.lt_of_le_of_lt _ h
    apply Nat.le_add_right
  refine (Nat.mul_lt_mul_left' ?_).mp h
  apply Nat.pos_of_ne_zero
  intro rfl
  rw [Nat.zero_mul, Nat.zero_mul] at h
  contradiction

end Nat
