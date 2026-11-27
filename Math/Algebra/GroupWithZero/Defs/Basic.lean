module

public import Math.Algebra.MonoidWithZero.Defs.Basic
public import Math.Algebra.Group.Units
public import Math.Algebra.GroupWithZero.Syntax
public import Math.Data.Int.Defs

namespace Math

public class GroupWithZeroOps (α: Type*) extends MonoidOps α, Zero α, CheckedInv? α, CheckedDiv? α, CheckedZPow? α where

public class IsLawfulDiv? (α: Type*) [Mul α] [Zero α] [CheckedDiv? α] [CheckedInv? α] where
  div?_eq_mul_inv? (a b: α) (h: b ≠ 0) : a /? b = a * b⁻¹?

public class IsLawfulInv?Right (α: Type*) [Mul α] [Zero α] [CheckedInv? α] [One α] where
  mul_inv?_cancel (a: α) (h: a ≠ 0) : a * a⁻¹? = 1

public class IsLawfulInv?Left (α: Type*) [Mul α] [Zero α] [CheckedInv? α] [One α] where
  inv?_mul_cancel (a: α) (h: a ≠ 0) : a⁻¹? * a = 1

public class IsLawfulPowZ? (α: Type*) [Zero α] [Pow α ℕ] [CheckedZPow? α] [CheckedInv? α] where
  powz?_ofNat (a: α) (n: ℕ) : a ^? (n: ℤ) = a ^ n
  powz?_negSucc (a: α) (n: ℕ) (h: a ≠ 0) : a ^? (Int.negSucc n) = a⁻¹? ^ (n + 1)

public class IsGroupWithZero (α: Type*) [GroupWithZeroOps α] extends IsMonoidWithZero α,
  IsLawfulDiv? α, IsLawfulInv?Left α, IsLawfulPowZ? α, IsZeroNeOne α where

export IsLawfulDiv? (div?_eq_mul_inv?)
export IsLawfulInv?Right (mul_inv?_cancel)
export IsLawfulInv?Left (inv?_mul_cancel)
export IsLawfulPowZ? (powz?_ofNat powz?_negSucc)

section

variable [Zero α] [Mul α] [NoZeroDivisors α]

public theorem mul_ne_zero {a b: α} (ha: a ≠ 0) (hb: b ≠ 0) : a * b ≠ 0 := by
  intro g
  cases of_mul_eq_zero g <;> contradiction

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply mul_ne_zero <;> invert_tactic)

end

section

variable [GroupWithZeroOps α] [IsGroupWithZero α]

public instance : IsLeftCancel₀ α where
  of_mul_left₀ {k a b} hk h := by
    rw [←one_mul a, ←one_mul b, ←inv?_mul_cancel k,
      mul_assoc, mul_assoc, h]
    assumption
public instance : IsLawfulInv?Right α where
  mul_inv?_cancel a ha := by
    have : a⁻¹? ≠ 0 := by
      intro g
      have := inv?_mul_cancel a ha
      rw [g, zero_mul] at this
      exact zero_ne_one this
    apply of_mul_left₀ this
    rw [mul_one, ←mul_assoc, inv?_mul_cancel, one_mul]
public instance : IsRightCancel₀ α where
  of_mul_right₀ {k a b} hk h := by
    rwa [←mul_one a, ←mul_one b, ←mul_inv?_cancel k,
      ←mul_assoc, ←mul_assoc, h]

@[expose] public def toUnit : { a: α // a ≠ 0 } ↪ Unit α where
  toFun a := {
    val := a.val
    inv := a.val⁻¹?~(a.property)
    val_mul_inv := mul_inv?_cancel a.val a.property
    inv_mul_val := inv?_mul_cancel a.val a.property
  }
  injective := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    congr; exact congrArg Unit.val h

end
