module

import Math.Tactic.TypeStar

namespace Math

syntax "invert_tactic" : tactic
syntax "invert_tactic_trivial" : tactic
syntax "invert_tactic_trivial_low_priority" : tactic
syntax "pow_tactic" : tactic
syntax "pow_tactic_from_invert" : tactic
syntax "pow_tactic_trivial" : tactic

public theorem pow_from_invert_helper (P Q: Prop) (n: ℤ) (h: 0 ≤ n ∨ P) (g: P -> Q) : 0 ≤ n ∨ Q := by
  cases h
  left; assumption
  right; apply g
  assumption

public theorem pow_from_invert (P: Prop) (n: ℤ) (h: P) : 0 ≤ n ∨ P := by
  right
  assumption

public theorem inv_from_pow_negSucc (P: α -> Prop) (n: ℕ) (a: α) (h: 0 ≤ Int.negSucc n ∨ P a) : P a := by
  cases h
  contradiction
  assumption

public theorem pow_of_natCast (P: α -> Prop) (n: ℕ) (a: α) : 0 ≤ (n: ℤ) ∨ P a := by
  left; apply Int.zero_le_ofNat

public theorem pow_of_negSucc (P: α -> Prop) (n: ℕ) (a: α) (h: P a) : 0 ≤ (Int.negSucc n) ∨ P a := by
  right; assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply NeZero.ne)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply inv_from_pow_negSucc <;> assumption)
| `(tactic|invert_tactic_trivial_low_priority) => `(tactic|assumption)
| `(tactic|invert_tactic) => `(tactic|first|assumption|trivial|invert_tactic_trivial|invert_tactic_trivial_low_priority)
| `(tactic|pow_tactic) => `(tactic|first|assumption|trivial|pow_tactic_from_invert|pow_tactic_trivial)
| `(tactic|pow_tactic_from_invert) => `(tactic|
  apply pow_from_invert_helper;
  assumption;
  intro;
  invert_tactic)

macro_rules
| `(tactic|pow_tactic_trivial) => `(tactic|apply pow_from_invert <;> invert_tactic)
macro_rules
| `(tactic|pow_tactic_trivial) => `(tactic|apply pow_of_natCast)
macro_rules
| `(tactic|pow_tactic_trivial) => `(tactic|apply pow_of_negSucc; invert_tactic)
