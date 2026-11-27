module

public import Math.Algebra.Semigroup.Defs.Basic
public import Math.Logic.Nontrivial
public import Math.Logic.LEM
public import Math.Data.Equiv.Ext

namespace Math

section Property

public class NoZeroDivisors (α: Type*) [Mul α] [Zero α] where
  of_mul_eq_zero {a b: α} (h: a * b = 0) : a = 0 ∨ b = 0

export NoZeroDivisors (of_mul_eq_zero)

public class IsZeroNeOne (α: Type*) [Zero α] [One α] : Prop where
  zero_ne_one : (0: α) ≠ (1: α)

export IsZeroNeOne (zero_ne_one)

public class IsLawfulOne (α: Type*) [Mul α] [One α] : Prop where
  mul_one (a: α) : a * 1 = a
  one_mul (a: α) : 1 * a = a
public class IsLawfulZero (α: Type*) [Add α] [Zero α] : Prop where
  add_zero (a: α) : a + 0 = a
  zero_add (a: α) : 0 + a = a
public class IsLawfulZeroMul (α: Type*) [Mul α] [Zero α] : Prop where
  mul_zero (a: α) : a * 0 = 0
  zero_mul (a: α) : 0 * a = 0
public class IsLawfulPowN (α: Type*) [Pow α ℕ] [Mul α] [One α] : Prop where
  pown_zero (a: α) : a ^ 0 = 1
  pown_succ (a: α) (n: ℕ) : a ^ (n + 1) = a ^ n * a
public class IsLawfulNSMul (α: Type*) [SMul ℕ α] [Add α] [Zero α] : Prop where
  zero_nsmul (a: α) : 0 • a = 0
  succ_nsmul (a: α) (n: ℕ) : (n + 1) • a = n • a + a

export IsLawfulOne (one_mul mul_one)
export IsLawfulZero (zero_add add_zero)
export IsLawfulZeroMul (zero_mul mul_zero)
export IsLawfulPowN (pown_zero pown_succ)
export IsLawfulNSMul (zero_nsmul succ_nsmul)

public instance (priority := 100) NoZeroDivisors.ofLeftCancel₀ [Mul α] [Zero α] [IsLawfulZeroMul α] [IsLeftCancel₀ α] [ExcludedMiddleEq α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply LEM.or_iff_not_imp_left.mpr
    intro ha
    rw [←mul_zero a] at h
    exact of_mul_left₀ ha h
public instance (priority := 100) [Mul α] [Zero α] [IsLawfulZeroMul α] [IsRightCancel₀ α] [ExcludedMiddleEq α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply LEM.or_iff_not_imp_right.mpr
    intro hb
    rw [←zero_mul b] at h
    exact of_mul_right₀ hb h

public instance [Add α] [Zero α] [IsLawfulZero α] : IsLawfulOne (MulOfAdd α) where
  mul_one := add_zero (α := α)
  one_mul := zero_add (α := α)
public instance [Mul α] [One α] [IsLawfulOne α] : IsLawfulZero (AddOfMul α) where
  add_zero := mul_one (α := α)
  zero_add := one_mul (α := α)

namespace DefaultPowN

public def default_pown [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) : ℕ -> α
| 0 => 1
| n + 1 => default_pown a n * a

public def fast_pown [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) (n: ℕ) : α :=
  if n = 0 then
    1
  else
    let x := fast_pown a (n / 2)
    x * x * (if n % 2 == 0 then 1 else a)

instance [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) (n: ℕ) :
  IsCommAt a (default_pown a n) where
  mul_comm := by
    induction n with
    | zero =>
      unfold default_pown
      rw [mul_one, one_mul]
    | succ n ih =>
      unfold default_pown
      rw [←mul_assoc, ih]

theorem nat_succ_div_two (n: ℕ) : (n + 1) / 2 =
  n / 2 + 1 / 2 + if 2 ≤ n % 2 + 1 % 2 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 2) / 2 = _
    rw [Nat.add_div_right _ (by decide), ih]
    dsimp; clear ih
    rw [Nat.add_assoc]; congr 1
    rw [Nat.add_mod]
    dsimp
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> (rw [h]; rfl)

theorem default_pown_step_half [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) (n: ℕ) :
  default_pown a n = default_pown a (n / 2) * default_pown a (n / 2) * (if n % 2 == 0 then 1 else a) := by
  induction n with
  | zero =>
    show 1 = 1 * 1 * 1
    iterate 2 rw [mul_one]
  | succ n ih =>
    rw [nat_succ_div_two]
    dsimp; rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [h, show (n + 1) % 2 = 1 by omega]
      rw [default_pown, ih, h]
      dsimp; rw [mul_one]
    · rw [h, show (n + 1) % 2 = 0 by omega]
      dsimp; rw [mul_one]
      unfold default_pown
      rw [ih, h]
      dsimp
      rw [mul_assoc _ _ (_ * _)]
      rw [mul_assoc, mul_assoc]; congr 1
      rw [←mul_assoc, ←mul_assoc]; congr 1
      rw [mul_comm]

@[csimp]
public theorem default_pown_eq_fast_pown : @default_pown = @fast_pown := by
  ext α _ _ _ _ a n
  induction n using fast_pown.induct a with
  | case1 => unfold default_pown fast_pown; dsimp
  | case2 n hn ih =>
    unfold fast_pown; rw [ite_eq_right hn, default_pown_step_half]
    congr

variable [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α]

public scoped instance instPowNat : Pow α ℕ where
  pow := default_pown

public scoped instance : IsLawfulPowN α where
  pown_zero _ := rfl
  pown_succ _ _ := rfl

end DefaultPowN

namespace DefaultNSMul

variable [Add α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α]

open scoped DefaultPowN

public scoped instance : SMul ℕ α where
  smul n a := MulOfAdd.get (Pow.pow (MulOfAdd.mk a) n)

public scoped instance : IsLawfulNSMul α where
  zero_nsmul _ := rfl
  succ_nsmul _ _ := rfl

end DefaultNSMul

public class MonoidOps (α: Type*) extends Mul α, One α where
  toPowN : Pow α ℕ

public instance [MonoidOps α] : Pow α ℕ := MonoidOps.toPowN
public instance (priority := 100) [Pow α ℕ] [Mul α] [One α] : MonoidOps α where
  toPowN := inferInstance

public class AddMonoidOps (α: Type*) extends Add α, Zero α where
  toNSMul : SMul ℕ α

public instance [AddMonoidOps α] : SMul ℕ α := AddMonoidOps.toNSMul
public instance (priority := 100) [SMul ℕ α] [Add α] [Zero α] : AddMonoidOps α where
  toNSMul := inferInstance

public class IsMonoid (α: Type*) [MonoidOps α] extends IsSemigroup α, IsLawfulOne α, IsLawfulPowN α where
public class IsAddMonoid (α: Type*) [AddMonoidOps α] extends IsAddSemigroup α, IsLawfulZero α, IsLawfulNSMul α where

end Property

section Basic

public instance [AddMonoidOps α] [IsLawfulNSMul α] : IsLawfulPowN (MulOfAdd α) where
  pown_zero := zero_nsmul (α := α)
  pown_succ := succ_nsmul (α := α)
public instance [MonoidOps α] [IsLawfulPowN α] : IsLawfulNSMul (AddOfMul α) where
  zero_nsmul := pown_zero (α := α)
  succ_nsmul := pown_succ (α := α)
public instance [MonoidOps α] [IsMonoid α] : IsAddMonoid (AddOfMul α) where
public instance [AddMonoidOps α] [IsAddMonoid α] : IsMonoid (MulOfAdd α) where

public instance : IsLawfulZeroMul ℕ where
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
public instance : IsLawfulZeroMul ℤ where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
public instance : IsLawfulOne ℕ where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
public instance : IsLawfulOne ℤ where
  one_mul := Int.one_mul
  mul_one := Int.mul_one
public instance : IsLawfulZero ℕ where
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
public instance : IsLawfulZero ℤ where
  zero_add := Int.zero_add
  add_zero := Int.add_zero
public instance : NoZeroDivisors ℕ := inferInstance
public instance : NoZeroDivisors ℤ := inferInstance

public instance : IsAddMonoid ℕ where
  zero_nsmul := Nat.zero_mul
  succ_nsmul n m := Nat.succ_mul m n
public instance : IsMonoid ℕ where
  pown_zero _ := rfl
  pown_succ _ _ := rfl
public instance : IsAddMonoid ℤ where
  zero_nsmul := Int.zero_mul
  succ_nsmul n m := by
    show (m + 1: ℤ) * n = m * n + n
    rw [Int.add_mul, one_mul]
public instance : IsMonoid ℤ where
  pown_zero := Int.pow_zero
  pown_succ := Int.pow_succ

theorem pown_succ_left [MonoidOps α] [IsMonoid α] (a: α) (n: ℕ) : a ^ (n + 1) = a * a ^ n := by
  induction n with
  | zero => rw [pown_succ, pown_zero, one_mul, mul_one]
  | succ n ih => rw (occs := [1]) [pown_succ, ih, mul_assoc, ←pown_succ]

theorem succ_nsmul_left [AddMonoidOps α] [IsAddMonoid α] (a: α) (n: ℕ) : (n + 1) • a = a + n • a :=
  pown_succ_left (α := MulOfAdd α) a n

public instance [Mul α] [One α] [IsLawfulOne α] : IsLawfulOne αᵐᵒᵖ where
  one_mul := mul_one (α := α)
  mul_one := one_mul (α := α)
public instance [Add α] [Zero α] [IsLawfulZero α] : IsLawfulZero αᵃᵒᵖ where
  zero_add := add_zero (α := α)
  add_zero := zero_add (α := α)
public instance [MonoidOps α] [IsMonoid α] : IsLawfulPowN αᵐᵒᵖ where
  pown_zero := pown_zero (α := α)
  pown_succ := pown_succ_left (α := α)
public instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulNSMul αᵃᵒᵖ where
  zero_nsmul := zero_nsmul (α := α)
  succ_nsmul := succ_nsmul_left (α := α)
public instance [MonoidOps α] [IsMonoid α] : IsMonoid αᵐᵒᵖ where
public instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid αᵃᵒᵖ where

end Basic
