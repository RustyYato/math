import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.AddMul.Order
import LeanMath.Order.Monotone

class IsZeroLEOne (α: Type*) [LE α] [LT α] [Zero α] [One α] extends IsPartialOrder α where
    protected zero_le_one : 0 ≤ (1: α)

class IsOrderedCommMonoid (α: Type*) [LE α] [LT α] [MonoidOps α] extends IsPartialOrder α, IsMonoid α, IsComm α where
    protected mul_le_mul_left: ∀{a b : α}, a ≤ b → ∀ k, k * a ≤ k * b

class IsOrderedAddCommMonoid (α: Type*) [LE α] [LT α] [AddMonoidOps α] extends IsPartialOrder α, IsAddMonoid α, IsAddComm α where
    protected add_le_add_left: ∀{a b : α}, a ≤ b → ∀ k, k + a ≤ k + b

class IsOrderedCancelCommMonoid (α: Type*) [LT α] [LE α] [MonoidOps α] extends IsOrderedCommMonoid α, IsLeftCancel α where
  protected le_of_mul_le_mul_left: ∀{a b k: α}, a * b ≤ a * k → b ≤ k

class IsOrderedCancelAddCommMonoid (α: Type*) [LT α] [LE α] [AddMonoidOps α] extends IsOrderedAddCommMonoid α, IsLeftAddCancel α where
  protected le_of_add_le_add_left: ∀{a b k: α}, a + b ≤ a + k → b ≤ k

def zero_le_one (α: Type*) [LE α] [LT α] [Zero α] [One α] [IsZeroLEOne α] : 0 ≤ (1: α) := IsZeroLEOne.zero_le_one

def zero_lt_one (α: Type*) [LE α] [LT α] [Zero α] [One α] [IsZeroLEOne α] [IsZeroNeOne α] : 0 < (1: α) := by
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  apply zero_le_one
  intro h
  exact zero_ne_one α (le_antisymm (zero_le_one _) h)

def mul_le_mul_left [LE α] [LT α] [MonoidOps α] [IsOrderedCommMonoid α]: ∀{a b : α}, a ≤ b → ∀ k, k * a ≤ k * b := IsOrderedCommMonoid.mul_le_mul_left
def add_le_add_left [LE α] [LT α] [AddMonoidOps α] [IsOrderedAddCommMonoid α]: ∀{a b : α}, a ≤ b → ∀ k, k + a ≤ k + b := IsOrderedAddCommMonoid.add_le_add_left
def le_of_mul_le_mul_left [LE α] [LT α] [MonoidOps α] [IsOrderedCancelCommMonoid α]: ∀{k a b: α}, k * a ≤ k * b → a ≤ b := IsOrderedCancelCommMonoid.le_of_mul_le_mul_left
def le_of_add_le_add_left [LE α] [LT α] [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α]: ∀{k a b: α}, k + a ≤ k + b → a ≤ b := IsOrderedCancelAddCommMonoid.le_of_add_le_add_left

def mul_le_mul_left_iff [LE α] [LT α] [MonoidOps α] [IsOrderedCancelCommMonoid α]: ∀{k a b: α}, k * a ≤ k * b ↔ a ≤ b := ⟨le_of_mul_le_mul_left, (mul_le_mul_left · _)⟩
def add_le_add_left_iff [LE α] [LT α] [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α]: ∀{k a b: α}, k + a ≤ k + b ↔ a ≤ b := ⟨le_of_add_le_add_left, (add_le_add_left · _)⟩

def mul_le_mul_right [LE α] [LT α] [MonoidOps α] [IsOrderedCommMonoid α]: ∀{a b : α}, a ≤ b → ∀ k, a * k ≤ b * k := by
  intro _ _ _ k
  rw [mul_comm _ k, mul_comm _ k]; apply mul_le_mul_left
  assumption
def add_le_add_right [LE α] [LT α] [AddMonoidOps α] [IsOrderedAddCommMonoid α]: ∀{a b : α}, a ≤ b → ∀ k, a + k ≤ b + k := by
  intro _ _ _ k
  rw [add_comm _ k, add_comm _ k]; apply add_le_add_left
  assumption
def le_of_mul_le_mul_right [LE α] [LT α] [MonoidOps α] [IsOrderedCancelCommMonoid α]: ∀{k a b: α}, a * k ≤ b * k → a ≤ b := by
  intro k _ _
  rw [mul_comm _ k, mul_comm _ k]; apply le_of_mul_le_mul_left
def le_of_add_le_add_right [LE α] [LT α] [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α]: ∀{k a b: α}, a + k ≤ b + k → a ≤ b := by
  intro k _ _
  rw [add_comm _ k, add_comm _ k]; apply le_of_add_le_add_left

def mul_le_mul_right_iff [LE α] [LT α] [MonoidOps α] [IsOrderedCancelCommMonoid α]: ∀{k a b: α}, a * k ≤ b * k ↔ a ≤ b := ⟨le_of_mul_le_mul_right, (mul_le_mul_right · _)⟩
def add_le_add_right_iff [LE α] [LT α] [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α]: ∀{k a b: α}, a + k ≤ b + k ↔ a ≤ b := ⟨le_of_add_le_add_right, (add_le_add_right · _)⟩

instance [LE α] [LT α] [AddMonoidOps α] [IsOrderedAddCommMonoid α] : IsOrderedCommMonoid (MulOfAdd α) where
  mul_le_mul_left := add_le_add_left (α := α)
instance [LE α] [LT α] [MonoidOps α] [IsOrderedCommMonoid α] : IsOrderedAddCommMonoid (AddOfMul α) where
  add_le_add_left := mul_le_mul_left (α := α)
instance [LE α] [LT α] [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α] : IsOrderedCancelCommMonoid (MulOfAdd α) where
  le_of_mul_le_mul_left := le_of_add_le_add_left (α := α)
instance [LE α] [LT α] [MonoidOps α] [IsOrderedCancelCommMonoid α] : IsOrderedCancelAddCommMonoid (AddOfMul α) where
  le_of_add_le_add_left := le_of_mul_le_mul_left (α := α)

instance : IsZeroLEOne ℕ where
  zero_le_one := by decide
instance : IsZeroLEOne ℤ where
  zero_le_one := by decide

instance : IsOrderedCancelAddCommMonoid ℕ where
  add_le_add_left := Nat.add_le_add_left
  le_of_add_le_add_left := Nat.le_of_add_le_add_left
instance : IsOrderedCancelAddCommMonoid ℤ where
  add_le_add_left := Int.add_le_add_left
  le_of_add_le_add_left := Int.le_of_add_le_add_left

instance : IsOrderedCommMonoid ℕ where
  mul_le_mul_left h _ := Nat.mul_le_mul_left _ h

section IsOrderedCommMonoid

variable [LE α] [LT α] [MonoidOps α] [IsOrderedCommMonoid α]

def mul_le_mul {a b c d: α} : a ≤ c -> b ≤ d -> a * b ≤ c * d := by
  intro ac bd; apply le_trans
  exact mul_le_mul_left bd _
  exact mul_le_mul_right ac _

def npow_le_npow {a b: α} : a ≤ b -> ∀n: ℕ, a ^ n ≤ b ^ n := by
  intro ab n
  induction n with
  | zero => rw [npow_zero, npow_zero]
  | succ n ih =>
    rw [npow_succ, npow_succ]
    apply mul_le_mul <;> assumption

def mul_lt_mul_left [IsLeftCancel α] {a b: α} : a < b -> ∀k, k * a < k * b := by
  intro ab k
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  apply mul_le_mul_left
  apply le_of_lt
  assumption
  intro g
  rw [of_mul_left (le_antisymm g (mul_le_mul_left (le_of_lt ab) _))] at ab
  exact Relation.irrefl ab

def mul_lt_mul_right [IsLeftCancel α] {a b: α} : a < b -> ∀k, a * k < b * k := by
  intro ab k; rw [mul_comm _ k ,mul_comm _ k]
  apply mul_lt_mul_left
  assumption

def mul_lt_mul [IsLeftCancel α] {a b c d: α} : a < c -> b < d -> a * b < c * d := by
  intro ac bd; apply lt_trans
  exact mul_lt_mul_left bd _
  exact mul_lt_mul_right ac _
def mul_lt_mul_of_lt_of_le [IsLeftCancel α] {a b c d: α} : a < c -> b ≤ d -> a * b < c * d := by
  intro ac bd; apply lt_of_le_of_lt
  exact mul_le_mul_left bd _
  exact mul_lt_mul_right ac _
def mul_lt_mul_of_le_of_lt [IsLeftCancel α] {a b c d: α} : a ≤ c -> b < d -> a * b < c * d := by
  intro ac bd; apply lt_of_lt_of_le
  exact mul_lt_mul_left bd _
  exact mul_le_mul_right ac _

def le_mul_left {a b: α} (h: 1 ≤ b) : a ≤ b * a := by
  rw (occs := [1]) [←one_mul a]
  apply mul_le_mul_right
  assumption

def le_mul_right {a b: α} (h: 1 ≤ b) : a ≤ a * b := by
  rw [mul_comm _ b]; apply le_mul_left; assumption

def one_le_mul {a b: α} (ha: 1 ≤ a) (hb: 1 ≤ b) : 1 ≤ a * b := by
  rw [←mul_one 1]
  apply mul_le_mul
  assumption
  assumption

def npow_strict_mono (n: ℕ) (h: 0 < n) [IsLeftCancel α] : StrictMonotone (α := α) (· ^ n) := by
  intro a b h; dsimp
  cases n with
  | zero => contradiction
  | succ n =>
  induction n with
  | zero => simpa [npow_one]
  | succ n ih =>
    rw [npow_succ a, npow_succ b]
    apply mul_lt_mul
    apply ih
    apply Nat.zero_lt_succ
    assumption

end IsOrderedCommMonoid

section IsOrderedAddCommMonoid

variable [LE α] [LT α] [AddMonoidOps α] [IsOrderedAddCommMonoid α]

def add_le_add {a b c d: α} : a ≤ c -> b ≤ d -> a + b ≤ c + d :=
  mul_le_mul (α := MulOfAdd α)

def nsmul_le_nsmul {a b: α} : a ≤ b -> ∀n: ℕ, n • a ≤ n • b :=
  npow_le_npow (α := MulOfAdd α)

def add_lt_add_left [IsLeftAddCancel α] {a b: α} : a < b -> ∀k, k + a < k + b :=
  mul_lt_mul_left (α := MulOfAdd α)

def add_lt_add_right [IsLeftAddCancel α] {a b: α} : a < b -> ∀k, a + k < b + k :=
  mul_lt_mul_right (α := MulOfAdd α)

def add_lt_add [IsLeftAddCancel α] {a b c d: α} : a < c -> b < d -> a + b < c + d :=
  mul_lt_mul (α := MulOfAdd α)
def add_lt_add_of_lt_of_le [IsLeftAddCancel α] {a b c d: α} : a < c -> b ≤ d -> a + b < c + d :=
  mul_lt_mul_of_lt_of_le (α := MulOfAdd α)
def add_lt_add_of_le_of_lt [IsLeftAddCancel α] {a b c d: α} : a ≤ c -> b < d -> a + b < c + d :=
  mul_lt_mul_of_le_of_lt (α := MulOfAdd α)

def le_add_left {a b: α} (h: 0 ≤ b) : a ≤ b + a :=
  le_mul_left (α := MulOfAdd α) h

def le_add_right {a b: α} (h: 0 ≤ b) : a ≤ a + b :=
  le_mul_right (α := MulOfAdd α) h

def nonneg_add {a b: α} (ha: 0 ≤ a) (hb: 0 ≤ b) : 0 ≤ a + b :=
  one_le_mul (α := MulOfAdd α) ha hb

def nsmul_strict_mono (n: ℕ) (h: 0 < n) [IsLeftAddCancel α] : StrictMonotone (α := α) (n • ·) :=
  npow_strict_mono (α := MulOfAdd α) n h

end IsOrderedAddCommMonoid

section IsOrderedCommMonoid

variable [LE α] [LT α] [MonoidOps α] [IsLeftCancel α] [DecidableLE α] [IsOrderedCommMonoid α] [IsLinearOrder α]

def le_of_npow_le_npow (a b: α) (n: ℕ) (h: 0 < n) : a ^ n ≤ b ^ n -> a ≤ b :=
  (npow_strict_mono n h).le_iff_le.mp

end IsOrderedCommMonoid

section IsOrderedAddCommMonoid

variable [LE α] [LT α] [AddMonoidOps α] [IsLeftAddCancel α] [DecidableLE α] [IsOrderedAddCommMonoid α] [IsLinearOrder α]

def le_of_nsmul_le_nsmul (a b: α) (n: ℕ) (h: 0 < n) : n • a ≤ n •  b -> a ≤ b :=
  (nsmul_strict_mono n h).le_iff_le.mp

end IsOrderedAddCommMonoid

section IsOrderedCancelCommMonoid

variable [LE α] [LT α] [MonoidOps α] [IsOrderedCancelCommMonoid α]

def lt_of_mul_lt_mul_left : ∀{k a b: α}, k * a < k * b → a < b := by
  intro k a b h; rw [lt_iff_le_and_not_ge] at *
  obtain ⟨h, g⟩ := h; apply And.intro
  apply le_of_mul_le_mul_left
  assumption
  intro g'; apply g
  apply mul_le_mul_left
  assumption

def lt_of_mul_lt_mul_right : ∀{k a b: α}, a * k < b * k → a < b := by
  intro k a b h; rw [mul_comm _ k, mul_comm _ k] at h
  apply lt_of_mul_lt_mul_left
  assumption

end IsOrderedCancelCommMonoid

section IsOrderedCancelAddCommMonoid

variable [LE α] [LT α] [AddMonoidOps α] [IsOrderedCancelAddCommMonoid α]

def lt_of_add_lt_add_left : ∀{k a b: α}, k + a < k + b → a < b :=
  lt_of_mul_lt_mul_left (α := MulOfAdd α)

def lt_of_add_lt_add_right : ∀{k a b: α}, a + k < b + k → a < b :=
  lt_of_mul_lt_mul_right (α := MulOfAdd α)

end IsOrderedCancelAddCommMonoid
