import LeanMath.Data.Nat.Sqrt
import LeanMath.Data.Equiv.Defs

namespace Nat

def pair (a b : ℕ) : ℕ :=
  if a < b then b * b + a else a * a + a + b

def unpair (n : ℕ) : ℕ × ℕ :=
  let s := sqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

@[simp]
def pair_unpair (n : ℕ) : pair (unpair n).1 (unpair n).2 = n := by
  dsimp only [unpair]; let s := sqrt n
  have sm : s * s + (n - s * s) = n := Nat.add_sub_cancel' (sq_sqrt _)
  split <;> (dsimp; rename_i h)
  · simp [s, pair, h, sm]
  · have hl : n - s * s - s ≤ s := Nat.sub_le_iff_le_add.2
      (Nat.sub_le_iff_le_add'.2 <| by rw [← Nat.add_assoc]; apply sqrt_le_add)
    simp [s, pair, Nat.not_lt.mpr hl, Nat.add_assoc, Nat.add_sub_cancel' (Nat.le_of_not_gt h), sm]

def pair_unpair' {n a b} (H : unpair n = (a, b)) : pair a b = n := by
  simpa [H] using pair_unpair n

@[simp]
def unpair_pair (a b : ℕ) : unpair (pair a b) = (a, b) := by
  dsimp only [pair]; split <;> rename_i h
  · show unpair (b * b + a) = (a, b)
    have be : sqrt (b * b + a) = b := (sqrt_add_eq _).mp (Nat.le_trans (Nat.le_of_lt h) (Nat.le_mul_of_pos_left b (by decide)))
    simp [unpair, be, Nat.add_sub_cancel_left, h]
  · show unpair (a * a + a + b) = (a, b)
    have ae : sqrt (a * a + (a + b)) = a := by
      rw [(sqrt_add_eq _).mp]
      rw [Nat.two_mul]
      exact Nat.add_le_add_left (Nat.le_of_not_gt h) _
    simp [unpair, ae, Nat.add_assoc, Nat.add_sub_cancel_left]
    intro g
    rw [←Nat.not_le] at g
    have := g  (Nat.le_add_right _ _)
    contradiction

@[simp]
def pair_eq_pair {a b c d : ℕ} : pair a b = pair c d ↔ a = c ∧ b = d := by
  apply Iff.intro
  intro h
  have : unpair (a.pair b) = unpair (c.pair d) := by rw [h]
  simp at this
  assumption
  rintro ⟨rfl, rfl⟩; rfl

@[simp]
theorem unpair_zero : unpair 0 = (0, 0) := by
  rw [unpair]
  simp

end Nat

def Equiv.nat_equiv_nat_sum_nat : ℕ ≃ (ℕ ⊕ ℕ) where
  toFun x := if x % 2 = 0 then .inl (x / 2) else .inr (x / 2)
  invFun
  | .inl x => 2 * x
  | .inr x => 2 * x + 1
  leftInv x := by
    cases x
    simp
    simp
    rw [Nat.mul_add_div]
    simp
    simp
  rightInv x := by
    simp
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    rw [if_pos h]
    dsimp
    rw [Nat.mul_div_cancel']
    exact Nat.dvd_of_mod_eq_zero h
    rw [if_neg]
    simp
    rw [←h]
    rw [Nat.div_add_mod]
    intro g
    rw [g] at h
    contradiction

def Equiv.nat_equiv_nat_prod_nat : ℕ ≃ (ℕ × ℕ) where
  toFun := Nat.unpair
  invFun x := Nat.pair x.1 x.2
  leftInv x := by simp
  rightInv x := by simp

def Equiv.int_equiv_nat_sum_nat : ℤ ≃ (ℕ ⊕ ℕ) where
  toFun
  | .ofNat x => .inl x
  | .negSucc x => .inr x
  invFun
  | .inl x => .ofNat x
  | .inr x => .negSucc x
  leftInv x := by cases x <;> rfl
  rightInv x := by cases x <;> rfl

def Equiv.int_equiv_nat : ℤ ≃ ℕ :=
  Equiv.int_equiv_nat_sum_nat.trans Equiv.nat_equiv_nat_sum_nat.symm
