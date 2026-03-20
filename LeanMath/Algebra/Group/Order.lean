import LeanMath.Algebra.Monoid.Order
import LeanMath.Algebra.Group.Defs

instance [LE α] [LT α] [GroupOps α] [IsOrderedCommMonoid α] [IsGroup α] : IsOrderedCancelCommMonoid α where
  le_of_mul_le_mul_left := by
    intro k a b h
    have := mul_le_mul_left h (k⁻¹)
    rwa [←mul_assoc, ←mul_assoc, inv_mul_cancel, one_mul, one_mul] at this

instance [LE α] [LT α] [AddGroupOps α] [IsOrderedAddCommMonoid α] [IsAddGroup α] : IsOrderedCancelAddCommMonoid α where
  le_of_add_le_add_left := le_of_mul_le_mul_left (α := MulOfAdd α)

section IsOrderedCommGroup

variable [LE α] [LT α] [GroupOps α] [IsGroup α] [IsOrderedCommMonoid α]

def div_le_iff_le_mul {a b c: α} : a / b ≤ c ↔ a ≤ c * b := by
  apply Iff.trans mul_le_mul_left_iff.symm
  rw [←mul_div_assoc, mul_div_cancel_left, mul_comm]

def le_mul_iff_div_le {a b c: α} : a ≤ b * c ↔ a / c ≤ b := div_le_iff_le_mul.symm

def le_div_iff_mul_le {a b c: α} : a ≤ b / c ↔ a * c ≤ b := by
  apply Iff.trans mul_le_mul_left_iff.symm
  rw [←mul_div_assoc, mul_div_cancel_left, mul_comm]

def mul_le_iff_le_div {a b c: α} : a * b ≤ c ↔ a ≤ c / b := le_div_iff_mul_le.symm

def div_lt_iff_lt_mul {a b c: α} : a / b < c ↔ a < c * b := by
  rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge,
    div_le_iff_le_mul, le_div_iff_mul_le]

def lt_mul_iff_div_lt {a b c: α} : a < b * c ↔ a / c < b := div_lt_iff_lt_mul.symm

def lt_div_iff_mul_lt {a b c: α} : a < b / c ↔ a * c < b := by
  rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge,
    div_le_iff_le_mul, le_div_iff_mul_le]

def mul_lt_iff_lt_div {a b c: α} : a * b < c ↔ a < c / b := lt_div_iff_mul_lt.symm

def inv_le_inv {a b: α} : a ≤ b -> b⁻¹ ≤ a⁻¹ := by
  intro h
  apply le_of_mul_le_mul_left
  rw [mul_inv_cancel]
  apply le_of_mul_le_mul_right
  rwa [mul_assoc, inv_mul_cancel, one_mul, mul_one]

def inv_le_inv_iff {a b: α} : b⁻¹ ≤ a⁻¹ ↔ a ≤ b := by
  apply Iff.intro _ inv_le_inv
  intro h; rw [←inv_inv a, ←inv_inv b]
  exact inv_le_inv h

def inv_lt_inv {a b: α} : a < b -> b⁻¹ < a⁻¹ := by
  rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, inv_le_inv_iff, inv_le_inv_iff]
  exact id
def inv_lt_inv_iff {a b: α} : b⁻¹ < a⁻¹ ↔ a < b := by
  rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, inv_le_inv_iff, inv_le_inv_iff]

def inv_le_of_one_le {a: α} : 1 ≤ a -> a⁻¹ ≤ a := by
  intro h
  apply le_trans _ h
  rw [←one_inv]
  apply inv_le_inv
  assumption

def le_inv_of_le_one {a: α} : a ≤ 1 -> a ≤ a⁻¹ := by
  intro h
  apply le_trans h
  rw [←one_inv]
  apply inv_le_inv
  assumption

def inv_lt_of_one_lt {a: α} : 1 < a -> a⁻¹ < a := by
  intro h
  apply lt_trans _ h
  rw [←one_inv]
  apply inv_lt_inv
  assumption

def lt_inv_of_lt_one {a: α} : a < 1 -> a < a⁻¹ := by
  intro h
  apply lt_trans h
  rw [←one_inv]
  apply inv_lt_inv
  assumption

def one_le_of_inv_le [IsLinearOrder α] {a: α} : a⁻¹ ≤ a -> 1 ≤ a := by
  intro h; apply not_lt.mp
  intro g
  replace g := lt_inv_of_lt_one g
  exact Relation.irrefl (lt_of_le_of_lt h g)

def one_lt_of_inv_lt [IsLinearOrder α] {a: α} : a⁻¹ < a -> 1 < a := by
  intro h; apply not_le.mp
  intro g
  replace g := le_inv_of_le_one g
  exact Relation.irrefl (lt_of_lt_of_le h g)

def le_one_of_le_inv [IsLinearOrder α] {a: α} : a ≤ a⁻¹ -> a ≤ 1 := by
  intro h; apply not_lt.mp
  intro g
  replace g := inv_lt_of_one_lt g
  exact Relation.irrefl (lt_of_le_of_lt h g)

def lt_one_of_lt_inv [IsLinearOrder α] {a: α} : a < a⁻¹ -> a < 1 := by
  intro h; apply not_le.mp
  intro g
  replace g := inv_le_of_one_le g
  exact Relation.irrefl (lt_of_lt_of_le h g)

def div_le_div {a b c d: α} : a ≤ c -> d ≤ b -> a / b ≤ c / d := by
  intro ac db; rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_le_mul
  assumption
  apply inv_le_inv
  assumption

def div_lt_div {a b c d: α} : a < c -> d < b -> a / b < c / d := by
  intro ac db; rw [div_eq_mul_inv, div_eq_mul_inv]
  apply mul_lt_mul
  assumption
  apply inv_lt_inv
  assumption

end IsOrderedCommGroup

section IsOrderedAddCommGroup

variable [LE α] [LT α] [AddGroupOps α] [IsAddGroup α] [IsOrderedAddCommMonoid α]

def sub_le_iff_le_add {a b c: α} : a - b ≤ c ↔ a ≤ c + b :=
  div_le_iff_le_mul (α := MulOfAdd α)

def le_add_iff_sub_le {a b c: α} : a ≤ b + c ↔ a - c ≤ b := sub_le_iff_le_add.symm

def le_sub_iff_add_le {a b c: α} : a ≤ b - c ↔ a + c ≤ b :=
  le_div_iff_mul_le (α := MulOfAdd α)

def add_le_iff_le_sub {a b c: α} : a + b ≤ c ↔ a ≤ c - b := le_sub_iff_add_le.symm

def sub_lt_iff_lt_add {a b c: α} : a - b < c ↔ a < c + b :=
  div_lt_iff_lt_mul (α := MulOfAdd α)

def lt_add_iff_sub_lt {a b c: α} : a < b + c ↔ a - c < b := sub_lt_iff_lt_add.symm

def lt_sub_iff_add_lt {a b c: α} : a < b - c ↔ a + c < b :=
  lt_div_iff_mul_lt (α := MulOfAdd α)

def add_lt_iff_lt_sub {a b c: α} : a + b < c ↔ a < c - b := lt_sub_iff_add_lt.symm

def neg_le_neg {a b: α} : a ≤ b -> -b ≤ -a :=
  inv_le_inv (α := MulOfAdd α)

def neg_le_neg_iff {a b: α} : -b ≤ -a ↔ a ≤ b :=
  inv_le_inv_iff (α := MulOfAdd α)

def neg_lt_neg {a b: α} : a < b -> -b < -a :=
  inv_lt_inv (α := MulOfAdd α)
def neg_lt_neg_iff {a b: α} : -b < -a ↔ a < b :=
  inv_lt_inv_iff (α := MulOfAdd α)

def neg_le_of_nonneg {a: α} : 0 ≤ a -> -a ≤ a :=
  inv_le_of_one_le (α := MulOfAdd α)

def le_neg_of_nonpos {a: α} : a ≤ 0 -> a ≤ -a :=
  le_inv_of_le_one (α := MulOfAdd α)

def neg_lt_of_pos {a: α} : 0 < a -> -a < a :=
  inv_lt_of_one_lt (α := MulOfAdd α)

def lt_neg_of_neg {a: α} : a < 0 -> a < -a :=
  lt_inv_of_lt_one (α := MulOfAdd α)

def nonneg_of_neg_le [IsLinearOrder α] {a: α} : -a ≤ a -> 0 ≤ a :=
  one_le_of_inv_le (α := MulOfAdd α)

def pos_of_neg_lt [IsLinearOrder α] {a: α} : -a < a -> 0 < a :=
  one_lt_of_inv_lt (α := MulOfAdd α)

def nonpos_of_le_neg [IsLinearOrder α] {a: α} : a ≤ -a -> a ≤ 0 :=
  le_one_of_le_inv (α := MulOfAdd α)

def neg_of_lt_neg [IsLinearOrder α] {a: α} : a < -a -> a < 0 :=
  lt_one_of_lt_inv (α := MulOfAdd α)

def sub_le_sub {a b c d: α} : a ≤ c -> d ≤ b -> a - b ≤ c - d :=
  div_le_div (α := MulOfAdd α)

def sub_lt_sub {a b c d: α} : a < c -> d < b -> a - b < c - d :=
  div_lt_div (α := MulOfAdd α)

end IsOrderedAddCommGroup
