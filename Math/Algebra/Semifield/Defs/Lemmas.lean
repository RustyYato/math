module

public import Math.Algebra.GroupWithZero.Defs.Lemmas
public import Math.Algebra.Semiring.Defs.Lemmas
public import Math.Algebra.Semifield.Defs.Basic

namespace Math

variable [SemifieldOps α] [IsDivisionSemiring α]

public theorem add_div? (a b c: α) (h: c ≠ 0) : (a + b) /? c = a /? c + b /? c := by
  iterate 3 rw [div?_eq_mul_inv?]
  apply add_mul

public theorem div?_add_div? (a b c d: α) [IsCommAt b d] (hb: b ≠ 0) (hd: d ≠ 0) : a /? b + c /? d = (a * d + c * b) /? (b * d) := by
  iterate 3 rw [div?_eq_mul_inv?]
  apply of_mul_right₀ (k := b * d)
  invert_tactic
  rw [mul_assoc, inv?_mul_cancel, mul_one, add_mul]
  rw [mul_assoc, ←mul_assoc _ b, inv?_mul_cancel, one_mul]
  rw [mul_assoc, mul_comm b d, ←mul_assoc _ d, inv?_mul_cancel, one_mul]

public theorem half_add_half [NeZero ((2: ℕ): α)] (a: α) : a /? (2: ℕ) + a /? (2: ℕ) = a := by
  rw [←add_div?, ←two_mul, mul_comm _ a, mul_div?_assoc, div?_self, mul_one]

@[expose] public def midpoint [NeZero ((2: ℕ): α)] (a b: α) := (a + b) /? (2: ℕ)

public theorem midpoint_comm [NeZero ((2: ℕ): α)] (a b: α) : midpoint a b = midpoint b a := by
  unfold midpoint; rw [add_comm]
