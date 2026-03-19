import LeanMath.Algebra.Semifield.Defs
import LeanMath.Algebra.Semiring.Order

def ne_zero_of_pos [LE α] [LT α] [IsPreorder α] [Zero α] (a: α) (ha: 0 < a) : a ≠ 0 := by
  intro rfl
  exact Relation.irrefl ha

variable [SemifieldOps α] [IsSemifield α] [LE α] [LT α] [IsOrderedSemiring α]
  -- [IsORCanMo]

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply ne_zero_of_pos; assumption)

def mul_lt_mul_of_pos_left: ∀(a b : α), a < b → ∀ (c : α), 0 < c → c * a < c * b := by
  intro a b ab c cpos
  apply lt_of_le_of_ne
  apply mul_le_mul_of_nonneg_left
  apply le_of_lt
  assumption
  apply le_of_lt
  assumption
  intro h
  have : c ≠ 0 := by symm; apply ne_of_lt; assumption
  have : c⁻¹? * (c * a) = c⁻¹? * (c * b) := by rw [h]
  rw [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this
  subst b
  exact Relation.irrefl ab

def mul_lt_mul_of_pos_right: ∀(a b : α), a < b → ∀ (c : α), 0 < c → a * c < b * c := by
  intro a b ab c cpos
  apply lt_of_le_of_ne
  apply mul_le_mul_of_nonneg_right
  apply le_of_lt
  assumption
  apply le_of_lt
  assumption
  intro h
  have : c ≠ 0 := by symm; apply ne_of_lt; assumption
  have : (a * c) * c⁻¹? = (b * c) * c⁻¹? := by rw [h]
  rw [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
  subst b
  exact Relation.irrefl ab

variable [IsLinearOrder α] [IsZeroLEOne α]

def pos_inv? (a: α) (ha: 0 < a) : 0 < a⁻¹? := by
  apply not_le.mp
  intro g
  rcases lt_or_eq_of_le g with g | g
  have := mul_lt_mul_of_pos_left _ _ g _ ha
  rw [mul_inv?_cancel, mul_zero] at this
  exact Relation.asymm this (zero_lt_one _)
  have : a * a⁻¹? = 1 := by rw [mul_inv?_cancel]
  rw [g, mul_zero] at this
  exact zero_ne_one _ this

local macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply natCast_ne_zero)

variable [IsOrderedCancelAddCommMonoid α]

def pos_mul_of_pos (a b: α) (ha: 0 < a) (hb: 0 < b) : 0 < a * b := by
  rw [lt_iff_le_and_not_ge] at *
  obtain ⟨ha, ga⟩ := ha
  obtain ⟨hb, gb⟩ := hb
  apply And.intro
  apply mul_nonneg
  assumption
  assumption
  intro g
  rcases of_mul_eq_zero (le_antisymm g (mul_nonneg ha hb)) with rfl | rfl <;> contradiction

def pos_div?_natCast (a: α) (ha: 0 < a) (n: ℕ) : 0 < a /? (n + 1: ℕ) := by
  rw [div?_eq_mul_inv?]
  apply pos_mul_of_pos
  assumption
  apply pos_inv?
  apply pos_natCast
