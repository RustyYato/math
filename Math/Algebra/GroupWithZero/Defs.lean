module

public import Math.Algebra.MonoidWithZero.Defs
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
    rw [←mul_one a, ←mul_one b, ←mul_inv?_cancel k,
      ←mul_assoc, ←mul_assoc, h]
    assumption

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

public theorem of_mul_ne_zero {a b: α} (h: a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  apply And.intro
  · intro rfl
    rw [zero_mul] at h
    contradiction
  · intro rfl
    rw [mul_zero] at h
    contradiction

macro_rules
| `(tactic|invert_tactic_trivial_low_priority) => `(tactic|first|apply (of_mul_ne_zero (by assumption)).left|apply (of_mul_ne_zero (by assumption)).right)

public instance [ExcludedMiddleEq α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply LEM.or_iff_not_imp_right.mpr
    intro g
    have : (a * b) * b⁻¹? = 0 := by rw [h, zero_mul]
    rw [mul_assoc, mul_inv?_cancel, mul_one] at this
    assumption

public theorem inv_ne_zero {a: α} (h: a ≠ 0) : a⁻¹? ≠ 0 := by
  intro g
  have : a * a⁻¹? = 0 := by rw [g, mul_zero]
  rw [mul_inv?_cancel] at this
  exact zero_ne_one this.symm

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply inv_ne_zero <;> invert_tactic)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|symm; apply zero_ne_one)

section

variable [NoZeroDivisors α]

public theorem div?_ne_zero {a b: α} (ha: a ≠ 0) (hb: b ≠ 0) : a /? b ≠ 0 := by
  rw [div?_eq_mul_inv?]
  invert_tactic

public theorem pown_ne_zero {a: α} {n: ℕ} (ha: a ≠ 0) : a ^ n ≠ 0 := by
  induction n with
  | zero =>
    rw [pown_zero]
    invert_tactic
  | succ n =>
    rw [pown_succ]
    apply mul_ne_zero
    assumption
    assumption

public theorem powz?_ne_zero {a: α} {n: ℤ} (ha: a ≠ 0) : a ^? n ≠ 0 := by
  cases n with
  | ofNat n =>
    dsimp; rw [powz?_ofNat]
    apply pown_ne_zero
    assumption
  | negSucc n =>
    rw [powz?_negSucc]
    apply pown_ne_zero
    invert_tactic
    invert_tactic

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply div?_ne_zero <;> invert_tactic)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply pown_ne_zero <;> invert_tactic)

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|first|apply powz?_ne_zero <;> invert_tactic)

end

public theorem eq_inv?_of_mul (a b: α) (h: a * b = 1) : a = b⁻¹?~(by
  intro g; rw [g, mul_zero] at h
  exact zero_ne_one h) := by
  have : b ≠ 0 := by
    intro g; rw [g, mul_zero] at h
    exact zero_ne_one h
  rw [←one_mul (b⁻¹?), ←h, mul_assoc, mul_inv?_cancel, mul_one]

public theorem inv?_eq_of_mul (a b: α) (h: a * b = 1) : a⁻¹?~(by
  intro g; rw [g, zero_mul] at h
  exact zero_ne_one h) = b := by
  have : a ≠ 0 := by
    intro g; rw [g, zero_mul] at h
    exact zero_ne_one h
  rw [←mul_one (a⁻¹?), ←h, ←mul_assoc, inv?_mul_cancel, one_mul]

public theorem one_inv? : (1: α)⁻¹? = 1 := by
  apply inv?_eq_of_mul
  rw [mul_one]

@[expose] public def ofUnit : Unit α ↪* α where
  toFun a := a.val
  map_one := rfl
  map_mul _ _ := rfl
  injective := by
    intro a b h
    ext; assumption

public theorem div?_self (a: α) (h: a ≠ 0) : a /? a = 1 := by
  rw [div?_eq_mul_inv?, mul_inv?_cancel]

public instance (a b: α) (h: a ≠ 0) [IsCommAt a b] : IsCommAt a⁻¹? b where
  mul_comm := by
    apply of_mul_left₀ (k := a)
    assumption
    rw [←mul_assoc, ←mul_assoc, mul_inv?_cancel, one_mul,
      mul_comm a, mul_assoc, mul_inv?_cancel, mul_one]

public instance (a b: α) (h: a ≠ 0) [IsCommAt a b] : IsCommAt b a⁻¹? := inferInstance

instance (a b c: α) (h: c ≠ 0) [IsCommAt a b] [IsCommAt c b] : IsCommAt (a /? c) b where
  mul_comm := by
    rw [div?_eq_mul_inv?, mul_assoc, mul_comm _ b, ←mul_assoc,
      mul_comm _ b, mul_assoc]

public instance (a b c: α) (h: c ≠ 0) [IsCommAt a b] [IsCommAt c b] : IsCommAt b (a /? c) := inferInstance

public theorem inv?_mul_rev (a b: α) (h: a * b ≠ 0) : (a * b)⁻¹? = b⁻¹? * a⁻¹? := by
  symm; apply eq_inv?_of_mul
  rw [mul_assoc, ←mul_assoc _ a, inv?_mul_cancel, one_mul, inv?_mul_cancel]

public theorem inv?_inv? (a: α) (h: a ≠ 0) : a⁻¹?⁻¹? = a := by
  symm; apply eq_inv?_of_mul
  rw [mul_inv?_cancel]

public theorem inv?_div? [NoZeroDivisors α] (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : (a /? b)⁻¹? = b /? a := by
  symm; apply eq_inv?_of_mul
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, ←mul_assoc,
    mul_assoc b, inv?_mul_cancel, mul_one, mul_inv?_cancel]

public theorem mul_div?_assoc (a b c: α) (h: c ≠ 0) : (a * b) /? c = a * (b /? c) := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, mul_assoc]

public theorem div?_mul (a b c: α) (h: b * c ≠ 0) : a /? (b * c) = a /? c /? b := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, div?_eq_mul_inv?,
    inv?_mul_rev, mul_assoc]

public theorem div?_div? [NoZeroDivisors α] (a b c: α) (hb: b ≠ 0) (hc: c ≠ 0) : a /? c /? b = a /? (b * c) := by
  rw [div?_mul]

public theorem mul_div?_comm (a b c: α) [IsCommAt b c] (h: b ≠ 0) : a * c /? b = a /? b * c := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?,
    mul_assoc, mul_assoc, mul_comm _ c]

public theorem div?_mul_cancel (a b: α) (h: b ≠ 0) : a /? b * b = a := by
  rw [div?_eq_mul_inv?, mul_assoc, inv?_mul_cancel, mul_one]

public theorem div?_one (a: α) : a /? 1 = a := by
  rw [div?_eq_mul_inv?, one_inv?, mul_one]

public theorem one_div? (a: α) (ha: a ≠ 0) : 1 /? a = a⁻¹? := by
  rw [div?_eq_mul_inv?, one_mul]

public theorem one_powz? (z: ℤ) : (1: α) ^? z = 1 := by
  cases z
  rw [powz?_ofNat, one_pown]
  rw [powz?_negSucc, one_inv?, one_pown]
  invert_tactic

public theorem inv?_pown [NoZeroDivisors α] (a: α) (n: ℕ) (h: a ≠ 0) : (a⁻¹?) ^ n = (a ^ n)⁻¹? := by
  apply eq_inv?_of_mul
  rw [←mul_pown, inv?_mul_cancel, one_pown]

public theorem mul_powz? [NoZeroDivisors α] (a b: α) (z: ℤ) (h: 0 ≤ z ∨ a * b ≠ 0) [IsCommAt a b] : (a * b) ^? z = a ^? z * b ^? z := by
  cases z
  iterate 3 rw [powz?_ofNat]
  rw [mul_pown]
  iterate 3 rw [powz?_negSucc, inv?_pown]
  rw [←inv?_mul_rev]; congr
  rw [←mul_pown, mul_comm]
  all_goals
    cases h; contradiction
    invert_tactic

public theorem powz?_zero (a: α) : a ^? 0 = 1 := by
  apply Eq.trans
  apply powz?_ofNat
  rw [pown_zero]

public theorem powz?_one (a: α) : a ^? 1 = a := by
  apply Eq.trans
  apply powz?_ofNat
  rw [pown_one]

public theorem powz?_neg_one (a: α) (h: a ≠ 0) : a ^? (-1) = a⁻¹? := by
  apply Eq.trans
  apply powz?_negSucc
  assumption
  rw [pown_one]

public theorem inv?_powz? (a: α) (n: ℤ) (h: a ≠ 0) : a⁻¹? ^? n = a ^? (-n) := by
  cases n <;> rename_i n
  rw [powz?_ofNat]
  cases n
  show _ = a ^? 0
  rw [pown_zero, powz?_zero]
  show _ = a ^? (Int.negSucc _)
  rw [powz?_negSucc]
  cases n; simp
  erw [powz?_neg_one, inv?_inv?, powz?_one]
  invert_tactic; simp
  rw [powz?_negSucc, inv?_inv?]
  show _ = a ^? (Nat.cast (_ + 1 + 1))
  rw [powz?_ofNat]
  invert_tactic

public theorem toUnit_mul
  (a b: α) (h: a * b ≠ 0) : toUnit ⟨a * b, h⟩ = toUnit ⟨a, by invert_tactic⟩ * toUnit ⟨b, by invert_tactic⟩ := by
  ext; rfl
public theorem toUnit_mul'
  [NoZeroDivisors α]
  (a b: α) (ha: a ≠ 0) (hb: b ≠ 0) : toUnit ⟨a, by invert_tactic⟩ * toUnit ⟨b, by invert_tactic⟩ =  toUnit ⟨a * b, by invert_tactic⟩ := by
  ext; rfl
public theorem toUnit_powz?
  [NoZeroDivisors α]
  (a: α) (n: ℤ) (h: a ≠ 0) : toUnit ⟨a ^? n, by invert_tactic⟩ = toUnit ⟨a, by invert_tactic⟩ ^ n := by
  ext; rcases n with n | n
  apply powz?_ofNat
  apply powz?_negSucc
public theorem toUnit_inv?
  [NoZeroDivisors α]
  (a: α) (h: a ≠ 0) : toUnit ⟨a⁻¹?, by invert_tactic⟩ = (toUnit ⟨a, by invert_tactic⟩)⁻¹ := by
  apply eq_inv_of_mul
  rw [toUnit_mul']
  ext; apply inv?_mul_cancel

public theorem powz?_add [NoZeroDivisors α] (a: α) (n m: ℤ) (h: a ≠ 0) : a ^? (n + m) = a ^? n * a ^? m := by
  apply Subtype.mk.inj
  apply toUnit.inj (a₁ := ⟨a ^? (n + m), by invert_tactic⟩) (a₂ := ⟨a ^? n * a ^? m, by invert_tactic⟩)
  rw [toUnit_mul]; iterate 3 rw [toUnit_powz?]
  rw [powz_add]
  assumption
public theorem powz?_mul [NoZeroDivisors α] (a: α) (n m: ℤ) (h: a ≠ 0) : a ^? (n * m) = (a ^? m) ^? n := by
  apply Subtype.mk.inj
  apply toUnit.inj (a₁ := ⟨a ^? (n * m), by invert_tactic⟩) (a₂ := ⟨(a ^? m) ^? n, by invert_tactic⟩)
  iterate 3 rw [toUnit_powz?]
  rw [powz_mul]
  all_goals invert_tactic
public theorem powz?_neg [NoZeroDivisors α] (a: α) (n: ℤ) (h: a ≠ 0) : a ^? (-n) = (a ^? n)⁻¹? := by
  apply Subtype.mk.inj
  apply toUnit.inj (a₁ := ⟨a ^? (-n), by invert_tactic⟩) (a₂ := ⟨(a ^? n)⁻¹?, by invert_tactic⟩)
  rw [toUnit_inv?]
  iterate 2 rw [toUnit_powz?]
  rw [powz_neg]
  all_goals invert_tactic

end
