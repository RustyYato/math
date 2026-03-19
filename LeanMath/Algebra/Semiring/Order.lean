import LeanMath.Algebra.MonoidWithZero.Order
import LeanMath.Algebra.Semiring.Defs

class IsOrderedNonUnitalNonAssocSemiring (α: Type*) [LT α] [LE α] [AddMonoidOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsOrderedAddCommMonoid α, IsOrderedZeroMul α where

class IsOrderedSemiring (α: Type*) [LT α] [LE α] [SemiringOps α] extends IsSemiring α, IsOrderedNonUnitalNonAssocSemiring α where

class IsStrictOrderedNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] [LT α] [LE α] extends IsOrderedNonUnitalNonAssocSemiring α where
  mul_pos: ∀{a b: α}, 0 < a -> 0 < b -> 0 < a * b

class IsStrictOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends
  IsOrderedSemiring α, IsStrictOrderedNonUnitalNonAssocSemiring α where

instance : IsStrictOrderedSemiring ℕ where
  mul_pos := Nat.mul_pos

instance : IsStrictOrderedSemiring ℤ where
  mul_pos := Int.mul_pos

section IsStrictOrderedSemiring

variable [LE α] [LT α] [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] [IsOrderedCancelAddCommMonoid α]
  [IsZeroLEOne α] [IsZeroNeOne α]

def nonneg_natCast (n: ℕ) : 0 ≤ (n: α) := by
  induction n with
  | zero => rw [natCast_zero]
  | succ n ih =>
    rw [natCast_succ]
    apply nonneg_add
    assumption
    apply zero_le_one

def natCast_le_natCast [IsLeftAddCancel α] (n m: ℕ) : (n: α) ≤ m ↔ n ≤ m := by
  induction n generalizing m with
  | zero =>
    simp; rw [natCast_zero]
    induction m with
    | zero => rw [natCast_zero]
    | succ n ih =>
      rw [natCast_succ]
      apply nonneg_add
      assumption
      apply zero_le_one
  | succ n ih =>
    cases m with
    | zero =>
      simp
      intro g
      rw [natCast_zero, natCast_succ] at g
      have : 1 ≤ (n: α) + 1 := by apply le_add_left; apply nonneg_natCast
      exact zero_ne_one _ (le_antisymm (zero_le_one _) (le_trans this g))
    | succ m =>
      simp; rw [←ih]
      rw [natCast_succ, natCast_succ]
      apply add_le_add_right_iff

def natCast_lt_natCast [IsLeftAddCancel α] (n m: ℕ) : (n: α) < m ↔ n < m := by
  rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, natCast_le_natCast, natCast_le_natCast]

def pos_natCast (n: ℕ) : (0: α) < (n + 1: ℕ) := by
  rw [←natCast_zero]
  apply (natCast_lt_natCast _ _).mpr
  apply Nat.zero_lt_succ
def natCast_ne_zero (n: ℕ) : (n + 1: ℕ) ≠ (0: α) := by
  intro h
  have := h ▸ pos_natCast (α := α) n
  exact Relation.irrefl this

end IsStrictOrderedSemiring

section IsStrictOrderedSemiring

variable [LE α] [LT α] [SemiringOps α] [IsOrderedSemiring α]

end IsStrictOrderedSemiring
