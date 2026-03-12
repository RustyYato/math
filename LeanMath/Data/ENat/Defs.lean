import LeanMath.Algebra.Semiring.Defs
import LeanMath.Order.Defs

inductive ENat where
| ofNat (n: Nat)
| inf
deriving DecidableEq

namespace ENat

scoped notation "ℕ∞" => ENat
scoped notation "∞" => ENat.inf

instance : NatCast ℕ∞ := ⟨.ofNat⟩
instance : OfNat ℕ∞ n := ⟨n⟩

instance : Add ℕ∞ where
  add
  | ∞, _ => ∞
  | _, ∞ => ∞
  | .ofNat a, .ofNat b => (a + b: ℕ)

instance : Mul ℕ∞ where
  mul
  | 0, ∞ => 0
  | ∞, 0 => 0
  | ∞, _ => ∞
  | _, ∞ => ∞
  | .ofNat a, .ofNat b => (a * b: ℕ)

instance : Max ℕ∞ where
  max
  | ∞, _ => ∞
  | _, ∞ => ∞
  | .ofNat a, .ofNat b => (a ⊔ b: ℕ)

instance : Min ℕ∞ where
  min
  | ∞, a => a
  | a, ∞ => a
  | .ofNat a, .ofNat b => (a ⊓ b: ℕ)

instance : SMul ℕ ℕ∞ where
  smul a b := a * b

instance : Pow ℕ∞ ℕ where
  pow
  | ∞, b =>
    match b with
    | 0 => 1
    | _ => ∞
  | .ofNat a, b => (a ^ b: ℕ)

@[cases_eliminator]
def cases {motive: ℕ∞ -> Prop}
  (natCast: ∀n: ℕ, motive n)
  (infty: motive ∞)
  (a: ℕ∞) : motive a := by cases a; apply natCast; apply infty

def mul_cases {motive: ℕ∞ -> Prop}
  (natCast_succ: ∀n: ℕ, motive (n + 1: ℕ))
  (zero: motive 0)
  (infty: motive ∞)
  (a: ℕ∞) : motive a := by
    cases a with
    | natCast a => cases a; apply zero; apply natCast_succ
    | infty => apply infty

def zero_eq_natCast : (0: ℕ∞) = (0: ℕ) := rfl
def one_eq_natCast : (1: ℕ∞) = (1: ℕ) := rfl

@[simp] def inf_add (a: ℕ∞) : ∞ + a = ∞ := rfl
@[simp] def add_inf (a: ℕ∞) : a + ∞ = ∞ := by cases a <;> rfl
@[simp] def add_natCast (a b: ℕ) : (a + b: ℕ∞) = (a + b: ℕ) := by cases a <;> rfl
@[simp] def inf_mul (a: ℕ∞) : ∞ * a = if a = 0 then 0 else ∞ := by cases a; rename_i n; cases n; all_goals rfl
@[simp] def mul_inf (a: ℕ∞) : a * ∞ = if a = 0 then 0 else ∞ := by cases a; rename_i n; cases n; all_goals rfl
@[simp] def mul_natCast (a b: ℕ) : (a * b: ℕ∞) = (a * b: ℕ) := by cases a <;> rfl
@[local simp] protected def zero_mul (a: ℕ∞) : 0 * a = 0 := by cases a <;> simp [zero_eq_natCast]
@[local simp] protected def mul_zero (a: ℕ∞) : a * 0 = 0 := by cases a <;> simp [zero_eq_natCast]
@[simp] def smul_eq_natCast_mul (n: ℕ) (a: ℕ∞) : n • a = n * a := rfl
@[simp] def inf_npow (n: ℕ) : ∞ ^ n = if n = 0 then 1 else ∞ := by cases n <;> rfl
@[simp] def natCast_npow (a n: ℕ) : (a: ℕ∞) ^ n = (a ^ n: ℕ) := rfl

@[simp] def natCast_succ_ne_zero (n: ℕ) : (n + 1: ℕ) ≠ (0: ℕ∞) := nofun

instance : IsAddMonoid ℕ∞ where
  add_assoc := by
    intro a b c;
    cases a; cases b; cases c
    all_goals simp [add_assoc]
  add_zero := by
    intro a
    cases a <;> simp [zero_eq_natCast]
  zero_add := by
    intro a
    cases a <;> simp [zero_eq_natCast]
  zero_nsmul := by
    intro a; cases a using mul_cases <;> simp [zero_eq_natCast]
  succ_nsmul := by
    intro n a; simp
    cases a using mul_cases <;> simp [zero_eq_natCast]
    rw [Nat.succ_mul]
    nofun

instance : IsComm ℕ∞ where
  mul_comm := by
    intro a b; cases a using mul_cases <;> cases b using mul_cases
    all_goals simp [mul_comm]

instance : IsLeftDistrib ℕ∞ where
  mul_add := by
    intro k a b
    cases k using mul_cases
    <;> cases a using mul_cases
    <;> cases b using mul_cases
    any_goals simp [mul_add]
    any_goals simp [add_zero, Nat.mul_succ, zero_add]
    nofun

instance : IsSemiring ℕ∞ where
  mul_assoc := by
    intro a b c;
    cases a using mul_cases
    cases b using mul_cases
    cases c using mul_cases
    any_goals simp [mul_assoc]
    nofun
    cases c using mul_cases
    simp; rw [if_pos rfl]; rfl
    simp
    cases b using mul_cases
    simp; cases c using mul_cases
    any_goals simp
    nofun
  add_comm := by
    intro a b
    cases a; cases b
    all_goals simp [add_comm]
  one_mul := by
    intro a
    cases a <;> simp [one_eq_natCast]
  mul_one := by
    intro a
    cases a <;> simp [one_eq_natCast]
  mul_zero := by
    intro a
    cases a <;> simp [zero_eq_natCast]
  zero_mul := by
    intro a
    cases a <;> simp [zero_eq_natCast]
  npow_zero a := by cases a <;> simp [one_eq_natCast]
  npow_succ a n := by
    cases a <;> simp [one_eq_natCast, npow_succ]
    split <;> nofun
  natCast_zero := rfl
  natCast_one := rfl
  natCast_succ _ := rfl

end ENat
