import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.GroupWithZero.Defs
import LeanMath.Algebra.Semiring.Char

class inductive NotChar2 (α: Type*) [AddMonoidOps α] [IsAddMonoid α] where
| intro (n: ℕ) : HasChar α n -> ¬n ∣ 2 -> NotChar2 α

instance [AddMonoidOps α] [IsAddMonoid α] [HasChar α 0] : NotChar2 α :=
  .intro 0 inferInstance (by decide)
instance [AddMonoidOps α] [IsAddMonoid α] [HasChar α (n + 3)] : NotChar2 α :=
  .intro (n + 3) inferInstance <| by
    intro h
    have := Nat.le_of_dvd (by decide) h
    have := Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ this)
    contradiction

def natCast_two_ne_zero [SemiringOps α] [IsSemiring α] [ha: NotChar2 α] : ((2: ℕ): α) ≠ 0 := by
  intro h
  obtain ⟨_, _, _⟩ := ha
  have dvd := HasChar.dvd_of_natCast_eq_zero _ h
  contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply natCast_two_ne_zero)

class SemifieldOps (α: Type*) extends GroupWithZeroOps α, SemiringOps α where

class IsDivisionSemiring (α: Type*) [SemifieldOps α] : Prop extends IsSemiring α, IsGroupWithZero α, NoZeroDivisors α where
class IsSemifield (α: Type*) [SemifieldOps α] : Prop extends IsDivisionSemiring α, IsComm α where

section

variable [SemifieldOps α] [IsDivisionSemiring α]

def div?_add_div? (a b c d: α) [IsCommAt b d] (hb: b ≠ 0) (hd: d ≠ 0) : a /? b + c /? d = (a * d + c * b) /? (b * d) := by
  apply of_mul_right₀ (k := b * d)
  invert_tactic
  rw [div?_mul_cancel, add_mul, ←mul_assoc, div?_mul_cancel, mul_comm b d,
    ←mul_assoc, div?_mul_cancel]

def div?_mul_div? (a b c d: α) [IsCommAt b d] [IsCommAt b c] (hb: b ≠ 0) (hd: d ≠ 0) : (a /? b) * (c /? d) = (a * c) /? (b * d) := by
 rw [eq_div_iff_mul_eq, mul_comm b,
    div?_eq_mul_inv?,div?_eq_mul_inv?,
    mul_assoc, mul_assoc c, ←mul_assoc _ d, inv?_mul_cancel,
    one_mul, mul_comm c, ←mul_assoc, mul_assoc a,
    inv?_mul_cancel, mul_one]

def half_add_half [NeZero ((2: ℕ): α)] (a: α) : a /? (2: ℕ) + a /? (2: ℕ) = a := by
  rw [div?_add_div?, ←mul_add, ←natCast_add]
  simp [←natCast_mul]
  rw [mul_div?_assoc, div?_self, mul_one]

def natCast_div?_natCast (n m: ℕ) (h: m ∣ n) (hm: (m: α) ≠ 0 := by invert_tactic) : (n / m: ℕ) = (n: α) /? (m: α) := by
  apply of_mul_right₀
  assumption
  rw [div?_mul_cancel, ←natCast_mul, Nat.div_mul_cancel]
  assumption

def add_div? (a b k: α) (hk: k ≠ 0) : (a + b) /? k = a /? k + b /? k := by
  iterate 3 rw [div?_eq_mul_inv?]
  rw [add_mul]

def npow_div? (a b: α) [IsCommAt a b] (hb: b ≠ 0) (n: ℕ) : (a /? b) ^ n = a ^ n /? (b ^ n) := by
  apply (eq_div_iff_mul_eq _ _ _ _).mpr
  rw [←mul_npow, div?_mul_cancel]

def midpoint [NotChar2 α] (a b: α) : α := (a + b) /? (2: ℕ)

def midpoint_comm [NotChar2 α] (a b: α) : midpoint a b = midpoint b a := by
  unfold midpoint; rw [add_comm]

end

namespace OfEquiv

variable (f: α ≃ β)

protected scoped instance [ops: SemifieldOps β] : SemifieldOps (OfEquiv f) where

protected scoped instance [SemifieldOps β] [IsDivisionSemiring β] : IsDivisionSemiring (OfEquiv f) where

protected scoped instance [SemifieldOps β] [IsSemifield β] : IsSemifield (OfEquiv f) where

end OfEquiv
