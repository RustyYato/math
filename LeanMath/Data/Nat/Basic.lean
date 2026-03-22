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

def mul_lt_mul_right' {a b c : ℕ} : 0 < a → (b * a < c * a ↔ b < c) := by
  rw [Nat.mul_comm _ a, Nat.mul_comm _ a]
  apply mul_lt_mul_left'

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

def not_between_succ (n m: Nat) : n < m -> m < n + 1 -> False := by
  intro h g
  replace g := Nat.le_of_lt_succ g
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h g)

def le_iff_exists_sum (a b: Nat) : a ≤ b ↔ ∃k, b = a + k := by
  apply Iff.intro
  intro h
  exists b - a
  rw [Nat.add_sub_cancel' h]
  intro ⟨k, h⟩
  subst b
  apply Nat.le_add_right

def div_le_div_const (a b k: Nat) : a ≤ b -> a / k ≤ b / k := by
  intro ab
  induction b, k using Nat.div.inductionOn generalizing a with
  | base b k h =>
    rw [Nat.div_eq b, if_neg h, Nat.div_eq a, if_neg]
    apply Nat.le_refl
    intro ⟨kpos, g⟩
    apply h
    apply And.intro kpos
    apply Nat.le_trans <;> assumption
  | ind b k h ih =>
    rw [Nat.div_eq b, if_pos h, Nat.div_eq]
    obtain ⟨kpos, h⟩ := h
    split
    apply Nat.succ_le_succ
    apply ih
    apply Nat.sub_le_iff_le_add.mpr
    rw [Nat.sub_add_cancel]
    assumption
    assumption
    rename_i g
    replace g := not_and.mp g kpos
    apply Nat.zero_le

def div_mul_le_mul_div (a b c d: Nat) : a / c * (b / d) ≤ (a * b) / (c * d) := by
  by_cases h:0 < c ∧ 0 < d
  apply (Nat.le_div_iff_mul_le _).mpr
  have : a / c * (b / d) * (c * d) = (c * (a / c)) * (d * (b / d)) := by ac_rfl
  rw [this]; clear this
  apply Nat.mul_le_mul
  apply Nat.mul_div_le
  apply Nat.mul_div_le
  apply Nat.mul_pos
  exact h.left
  exact h.right
  cases Decidable.not_and_iff_or_not.mp h
  all_goals
    rename_i h
    cases Nat.le_zero.mp (Nat.not_lt.mp h)
    rw [Nat.div_zero]
  rw [Nat.zero_mul]
  all_goals apply Nat.zero_le

def two_dvd_mul_succ (n: Nat) : 2 ∣ n * (n + 1) := by
  cases Nat.mod_two_eq_zero_or_one n <;> rename_i h
  apply Nat.dvd_trans
  apply Nat.dvd_of_mod_eq_zero
  assumption
  apply Nat.dvd_mul_right
  apply flip Nat.dvd_trans
  apply Nat.dvd_mul_left
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, h]

def mul_eq_one_iff {a b: Nat} : a * b = 1 ↔ a = 1 ∧ b = 1 := by
  apply Iff.intro
  · intro h
    match a with
    | 0 => rw [Nat.zero_mul] at h; contradiction
    | 1 =>
      rw [Nat.one_mul] at h
      subst b
      trivial
    | a + 2 =>
    match b with
    | 0 => rw [Nat.mul_zero] at h; contradiction
    | b + 1 => simp [Nat.mul_add, Nat.add_mul, ←Nat.add_assoc] at h
  · intro ⟨h, g⟩
    rw [h, g]

def square_add (a b: Nat) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_assoc, Nat.two_mul]
  ac_rfl

def square_sub (a b: Nat) (h: b ≤ a) : (a - b) * (a - b) = a * a + b * b - 2 * a * b := by
  apply Int.ofNat_inj.mp
  rw [Nat.two_mul, Nat.add_mul, Int.ofNat_sub]
  simp [Int.ofNat_sub h, Int.sub_mul, Int.mul_sub]
  rw [Int.mul_comm b a]
  omega
  rw [le_iff_exists_sum] at *
  obtain ⟨k, h⟩ := h
  subst a
  exists k * k
  simp [Nat.add_mul, Nat.mul_add]
  ac_rfl

def of_le_pred_self (n: Nat) (h: n ≤ n.pred) : n = 0 := by
  cases n
  rfl
  have := Nat.not_lt_of_le h (Nat.lt_succ_self _)
  contradiction

def of_mul_add_lt {a b c d n: ℕ} (h: b < n) (g: d < n) (eq: n * a + b = n * c + d) : a = c ∧ b = d := by
  have : (n * a + b) % n = (n * c + d) % n := by rw [eq]
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt g] at this
  subst d
  simp at eq
  apply And.intro _ rfl
  have : (n * a) / n = (n * c) / n := by rw [eq]
  rwa [Nat.mul_div_cancel_left, Nat.mul_div_cancel_left] at this
  omega
  omega

def mul_add_lt (x y n: ℕ) (hx: x < n) (hy: y < m) : x * m + y < n * m := by
  match n with
  | n + 1 =>
  rw [Nat.succ_mul]
  apply Nat.add_lt_add_of_le_of_lt _ hy
  apply Nat.mul_le_mul_right
  apply Nat.le_of_lt_succ
  assumption

end Nat
