import LeanMath.Algebra.Semifield.Defs
import LeanMath.Algebra.Semiring.Order

def ne_zero_of_pos [LE α] [LT α] [IsPreorder α] [Zero α] (a: α) (ha: 0 < a) : a ≠ 0 := by
  intro rfl
  exact Relation.irrefl ha

variable [SemifieldOps α] [IsDivisionSemiring α] [LE α] [LT α] [IsOrderedSemiring α]
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

def lt_of_mul_lt_mul_of_pos_left: ∀(a b c : α), 0 < c → c * a < c * b -> a < b := by
  intro a b c cpos h
  have := mul_lt_mul_of_pos_left _ _ h (c⁻¹?) (pos_inv? _ cpos)
  rwa [←mul_assoc, ←mul_assoc, inv?_mul_cancel,
    one_mul, one_mul] at this

def lt_of_mul_lt_mul_of_pos_right: ∀(a b c : α), 0 < c → a * c < b * c -> a < b := by
  intro a b c cpos h
  have := mul_lt_mul_of_pos_right _ _ h (c⁻¹?) (pos_inv? _ cpos)
  rwa [mul_assoc, mul_assoc, mul_inv?_cancel,
    mul_one, mul_one] at this

def le_of_mul_le_mul_of_pos_left: ∀(a b c : α), 0 < c → c * a ≤ c * b -> a ≤ b := by
  intro a b c cpos ab
  have := mul_le_mul_of_nonneg_left ab c⁻¹? ?_
  rwa [←mul_assoc, ←mul_assoc, inv?_mul_cancel, one_mul, one_mul] at this
  apply le_of_lt
  apply pos_inv?
  assumption

def mul_le_mul_of_pos_right: ∀(a b c : α), 0 < c → a * c ≤ b * c -> a ≤ b := by
  intro a b c cpos ab
  have := mul_le_mul_of_nonneg_right ab c⁻¹? ?_
  rwa [mul_assoc, mul_assoc, mul_inv?_cancel, mul_one, mul_one] at this
  apply le_of_lt
  apply pos_inv?
  assumption

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

def pos_div? {a b: α} (ha: 0 < a) (hb: 0 < b) : 0 < a /? b := by
  rw [div?_eq_mul_inv?]
  apply pos_mul_of_pos
  assumption
  apply pos_inv?
  assumption

def pos_div?_natCast {a: α} (ha: 0 < a) (n: ℕ) : 0 < a /? (n + 1: ℕ) := by
  apply pos_div?
  assumption
  apply pos_natCast

def inv?_le_inv? [IsComm α] [IsZeroLEOne α]
  {a b: α} (ha: 0 < a) (h: a ≤ b) : b⁻¹?~(by
    have := lt_of_lt_of_le ha h
    invert_tactic) ≤ a⁻¹? := by
    apply le_of_mul_le_mul_of_pos_left
    assumption
    rw [mul_inv?_cancel]
    apply le_of_mul_le_mul_of_pos_left
    apply lt_of_lt_of_le _ h
    assumption
    rwa [mul_comm, mul_assoc, inv?_mul_cancel,
      mul_one, mul_one]

def inv?_lt_inv? [IsComm α] [IsZeroLEOne α]
  {a b: α} (ha: 0 < a) (h: a < b) : b⁻¹?~(by
    have := lt_trans ha h
    invert_tactic) < a⁻¹? := by
    apply lt_of_mul_lt_mul_of_pos_left
    assumption
    rw [mul_inv?_cancel]
    apply lt_of_mul_lt_mul_of_pos_left
    apply lt_trans _ h
    assumption
    rwa [mul_comm, mul_assoc, inv?_mul_cancel,
      mul_one, mul_one]

def of_inv?_le_inv? [IsComm α] [IsZeroLEOne α]
  {a b: α} (hb: 0 < b) (ha: a ≠ 0) (h: b⁻¹? ≤ a⁻¹?) : a ≤ b := by
    have := inv?_le_inv? ?_ h
    rwa [inv?_inv?, inv?_inv?] at this
    apply pos_inv?; assumption

def of_inv?_lt_inv? [IsComm α] [IsZeroLEOne α]
  {a b: α} (hb: 0 < b) (ha: a ≠ 0) (h: b⁻¹? < a⁻¹?) : a < b := by
    have := inv?_lt_inv? ?_ h
    rwa [inv?_inv?, inv?_inv?] at this
    apply pos_inv?; assumption
