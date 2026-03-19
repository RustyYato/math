import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.GroupWithZero.Defs

class SemifieldOps (α: Type*) extends GroupWithZeroOps α, SemiringOps α where

class IsDivisionSemiring (α: Type*) [SemifieldOps α] : Prop extends IsSemiring α, IsGroupWithZero α, NoZeroDivisors α where
class IsSemifield (α: Type*) [SemifieldOps α] : Prop extends IsDivisionSemiring α, IsComm α where

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply NeZero.ne)

variable [SemifieldOps α] [IsDivisionSemiring α]

def div?_add_div? (a b c d: α) [IsCommAt b d] (hb: b ≠ 0) (hd: d ≠ 0) : a /? b + c /? d = (a * d + c * b) /? (b * d) := by
  apply of_mul_right₀ (k := b * d)
  invert_tactic
  rw [div?_mul_cancel, add_mul, ←mul_assoc, div?_mul_cancel, mul_comm b d,
    ←mul_assoc, div?_mul_cancel]

def half_add_half [NeZero ((2: ℕ): α)] (a: α) : a /? (2: ℕ) + a /? (2: ℕ) = a := by
  rw [div?_add_div?, ←mul_add, ←natCast_add]
  simp [←natCast_mul]
  rw [mul_div?_assoc, div?_self, mul_one]
