module

public import Math.Algebra.Semifield.Defs
public import Math.Algebra.Ring.Defs

namespace Math

public class FieldOps (α: Type*) extends SemifieldOps α, RingOps α where

public instance
  [RingOps α] [CheckedInv? α]
  [CheckedDiv? α] [CheckedZPow? α]
   : FieldOps α where

public class IsDivisionRing (α: Type*) [FieldOps α] extends
  IsDivisionSemiring α, IsRing α where
public class IsField (α: Type*) [FieldOps α] extends
  IsDivisionRing α, IsSemifield α where

variable [FieldOps α] [IsDivisionRing α]

public theorem neg_div? (a b: α) (h: b ≠ 0) : (-a) /? b = -(a /? b) := by
  apply eq_neg_of_add
  rw [←add_div?, neg_add_cancel, zero_div?]

public theorem sub_div? (a b c: α) (h: c ≠ 0) : (a - b) /? c = a /? c - b /? c := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_div?, neg_div?]

public theorem div?_sub_div? (a b c d: α) [IsCommAt b d] (hb: b ≠ 0) (hd: d ≠ 0) : a /? b - c /? d = (a * d - c * b) /? (b * d) := by
  iterate 3 rw [div?_eq_mul_inv?]
  apply of_mul_right₀ (k := b * d)
  invert_tactic
  rw [mul_assoc, inv?_mul_cancel, mul_one, sub_mul]
  rw [mul_assoc, ←mul_assoc _ b, inv?_mul_cancel, one_mul]
  rw [mul_assoc, mul_comm b d, ←mul_assoc _ d, inv?_mul_cancel, one_mul]
