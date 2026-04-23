import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Semiring.Order
import LeanMath.Algebra.Group.Order
import LeanMath.Tactic.AxiomBlame

section

variable [LE α] [LT α] [RingOps α] [IsRing α] [IsOrderedZeroMul α]
  [IsOrderedAddCommMonoid α]

def mul_nonpos_of_nonpos_of_nonneg: ∀{a b: α}, a ≤ 0 -> 0 ≤ b -> a * b ≤ 0 := by
  intro a b ha hb
  rw [←neg_neg (a * b), neg_mul_left, ←neg_zero]
  apply neg_le_neg
  apply mul_nonneg
  rw [←neg_zero]
  apply neg_le_neg
  assumption
  assumption
def mul_nonpos_of_nonneg_of_nonpos: ∀{a b: α}, 0 ≤ a -> b ≤ 0 -> a * b ≤ 0 := by
  intro a b ha hb
  rw [←neg_neg (a * b), neg_mul_right, ←neg_zero]
  apply neg_le_neg
  apply mul_nonneg
  assumption
  rw [←neg_zero]
  apply neg_le_neg
  assumption

def nonneg_sq [IsLinearOrder α] (a: α) : 0 ≤ a ^ 2 := by
  rcases le_total 0 a
  rw [npow_two, ←mul_zero a]
  apply mul_le_mul_of_nonneg_left
  assumption
  assumption
  rw [←neg_sq, npow_two, ←mul_zero (-a)]
  have : 0 ≤ -a := by
    rw [←neg_zero]; apply neg_le_neg
    assumption
  apply mul_le_mul_of_nonneg_left
  assumption
  assumption

end

section IsStrictOrderedSemiring

variable [LE α] [LT α] [AddGroupWithOneOps α] [IsAddGroupWithOne α] [IsOrderedCancelAddCommMonoid α]
  [IsZeroLEOne α] [IsZeroNeOne α]

def intCast_le_intCast (n m: ℤ) : (n: α) ≤ m ↔ n ≤ m := by
  match n, m with
  | .ofNat n, .ofNat m => simp [intCast_ofNat, natCast_le_natCast]
  | .negSucc n, .negSucc m =>
    simp [intCast_negSucc, natCast_le_natCast, neg_le_neg_iff]
    apply Iff.intro
    intro h; omega
    intro h; omega
  | .negSucc n, .ofNat m =>
    simp [intCast_ofNat, intCast_negSucc]
    apply Iff.intro
    intro h; omega
    intro h
    apply le_trans
    apply neg_le_neg (a := 0)
    apply nonneg_natCast
    rw [neg_zero]
    apply nonneg_natCast
  | .ofNat n, .negSucc m =>
    simp [intCast_ofNat, intCast_negSucc]
    apply flip Iff.intro
    intro; exfalso
    omega; intro h; exfalso
    have := neg_lt_neg_iff.mpr <| (natCast_lt_natCast (α := α) 0 (m + 1)).mpr (Nat.zero_lt_succ _)
    rw [natCast_zero, neg_zero] at this
    exact not_le_of_lt (lt_of_le_of_lt h this) (nonneg_natCast _)

def intCast_lt_intCast [IsLeftAddCancel α] (n m: ℤ) : (n: α) < m ↔ n < m := by
  rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, intCast_le_intCast, intCast_le_intCast]

end IsStrictOrderedSemiring
