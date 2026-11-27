module

public import Math.Tactic.Basic
public import Math.Data.AddMul.Defs

namespace Math

section Property

public class IsSemigroup (α: Type*) [Mul α] : Prop where
  mul_assoc (a b c: α) : a * b * c = a * (b * c)

export IsSemigroup (mul_assoc)

public class IsAddSemigroup (α: Type*) [Add α] : Prop where
  add_assoc (a b c: α) : a + b + c = a + (b + c)

export IsAddSemigroup (add_assoc)

public class IsCommAt {α: Type*} [Mul α] (a b: α) where
  mul_comm: a * b = b * a
public class IsAddCommAt {α: Type*} [Add α] (a b: α) where
  add_comm: a + b = b + a

public class IsComm (α: Type*) [Mul α] where
  mul_comm (a b: α): a * b = b * a
public class IsAddComm (α: Type*) [Add α] where
  add_comm (a b: α): a + b = b + a

public instance (priority := 10_000) [Mul α] [IsComm α] (a b: α) : IsCommAt a b where
  mul_comm := IsComm.mul_comm _ _
public instance (priority := 10_000) [Add α] [IsAddComm α] (a b: α) : IsAddCommAt a b where
  add_comm := IsAddComm.add_comm _ _

public theorem mul_comm [Mul α] (a b: α) [IsCommAt a b] : a * b = b * a := IsCommAt.mul_comm
public theorem add_comm [Add α] (a b: α) [IsAddCommAt a b] : a + b = b + a := IsAddCommAt.add_comm

public instance (priority := 10) [Mul α] (a b: α) [IsCommAt a b] : IsCommAt b a where
  mul_comm := by
    rw [mul_comm a]

public instance (priority := 10) [Add α] (a b: α) [IsAddCommAt a b] : IsAddCommAt b a where
  add_comm := by
    rw [add_comm a]

public class IsLeftCancel (α: Type*) [Mul α] where
  of_mul_left {k a b: α} : k * a = k * b -> a = b
public class IsRightCancel (α: Type*) [Mul α] where
  of_mul_right {k a b: α} : a * k = b * k -> a = b

export IsLeftCancel (of_mul_left)
export IsRightCancel (of_mul_right)

public class IsLeftAddCancel (α: Type*) [Add α] where
  of_add_left {k a b: α} : k + a = k + b -> a = b
public class IsRightAddCancel (α: Type*) [Add α] where
  of_add_right {k a b: α} : a + k = b + k -> a = b

export IsLeftAddCancel (of_add_left)
export IsRightAddCancel (of_add_right)

public class IsLeftCancel₀ (α: Type*) [Mul α] [Zero α] where
  of_mul_left₀ {k a b: α} : k ≠ 0 -> k * a = k * b -> a = b
public class IsRightCancel₀ (α: Type*) [Mul α] [Zero α] where
  of_mul_right₀ {k a b: α} : k ≠ 0 -> a * k = b * k -> a = b

export IsLeftCancel₀ (of_mul_left₀)
export IsRightCancel₀ (of_mul_right₀)

public instance (priority := 500) [Mul α] [IsRightCancel α] [IsComm α] : IsLeftCancel α where
  of_mul_left {k a b} h := by
    rw [mul_comm k, mul_comm k] at h
    exact of_mul_right h
public instance (priority := 500) [Mul α] [IsLeftCancel α] [IsComm α] : IsRightCancel α where
  of_mul_right {k a b} h := by
    rw [mul_comm _ k, mul_comm _ k] at h
    exact of_mul_left h

public instance (priority := 500) [Add α] [IsRightAddCancel α] [IsAddComm α] : IsLeftAddCancel α where
  of_add_left {k a b} h := by
    rw [add_comm k, add_comm k] at h
    exact of_add_right h
public instance (priority := 500) [Add α] [IsLeftAddCancel α] [IsAddComm α] : IsRightAddCancel α where
  of_add_right {k a b} h := by
    rw [add_comm _ k, add_comm _ k] at h
    exact of_add_left h

public instance (priority := 500) [Mul α] [Zero α] [IsRightCancel₀ α] [IsComm α] : IsLeftCancel₀ α where
  of_mul_left₀ {k a b} k_ne_zero h := by
    rw [mul_comm k, mul_comm k] at h
    exact of_mul_right₀ k_ne_zero h
public instance (priority := 500) [Mul α] [Zero α] [IsLeftCancel₀ α] [IsComm α] : IsRightCancel₀ α where
  of_mul_right₀ {k a b} k_ne_zero h := by
    rw [mul_comm _ k, mul_comm _ k] at h
    exact of_mul_left₀ k_ne_zero h

end Property

section Basic

public instance [Mul α] [IsSemigroup α] : IsAddSemigroup (AddOfMul α) where
  add_assoc := mul_assoc (α := α)
public instance [Add α] [IsAddSemigroup α] : IsSemigroup (MulOfAdd α) where
  mul_assoc := add_assoc (α := α)
public instance [Mul α] [IsComm α] : IsAddComm (AddOfMul α) where
  add_comm a b := mul_comm (α := α) a.get b.get
public instance [Add α] [IsAddComm α] : IsComm (MulOfAdd α) where
  mul_comm a b := add_comm (α := α) a.get b.get
public instance [Mul α] [IsLeftCancel α] : IsLeftAddCancel (AddOfMul α) where
  of_add_left := of_mul_left (α := α)
public instance [Add α] [IsLeftAddCancel α] : IsLeftCancel (MulOfAdd α) where
  of_mul_left := of_add_left (α := α)
public instance [Mul α] [IsRightCancel α] : IsRightAddCancel (AddOfMul α) where
  of_add_right := of_mul_right (α := α)
public instance [Add α] [IsRightAddCancel α] : IsRightCancel (MulOfAdd α) where
  of_mul_right := of_add_right (α := α)

public instance [Mul α] [IsSemigroup α] : IsSemigroup αᵐᵒᵖ where
  mul_assoc _ _ _ := by ext; dsimp; rw [mul_assoc]
public instance [Add α] [IsAddSemigroup α] : IsAddSemigroup αᵃᵒᵖ where
  add_assoc _ _ _ := by ext; dsimp; rw [add_assoc]
public instance [Mul α] [IsComm α] : IsComm αᵐᵒᵖ where
  mul_comm _ _ := by ext; dsimp; rw [mul_comm]
public instance [Add α] [IsAddComm α] : IsAddComm αᵃᵒᵖ where
  add_comm _ _ := by ext; dsimp; rw [add_comm]
public instance [Mul α] [IsRightCancel α] : IsLeftCancel (αᵐᵒᵖ) where
  of_mul_left := of_mul_right (α := α)
public instance [Add α] [IsRightAddCancel α] : IsLeftAddCancel (αᵃᵒᵖ) where
  of_add_left := of_add_right (α := α)
public instance [Mul α] [IsLeftCancel α] : IsRightCancel (αᵐᵒᵖ) where
  of_mul_right := of_mul_left (α := α)
public instance [Add α] [IsLeftAddCancel α] : IsRightAddCancel (αᵃᵒᵖ) where
  of_add_right := of_add_left (α := α)

public instance : IsSemigroup ℕ where
  mul_assoc := Nat.mul_assoc
public instance : IsSemigroup ℤ where
  mul_assoc := Int.mul_assoc
public instance : IsAddSemigroup ℕ where
  add_assoc := Nat.add_assoc
public instance : IsAddSemigroup ℤ where
  add_assoc := Int.add_assoc

public instance : IsComm ℕ where
  mul_comm := Nat.mul_comm
public instance : IsComm ℤ where
  mul_comm := Int.mul_comm
public instance : IsAddComm ℕ where
  add_comm := Nat.add_comm
public instance : IsAddComm ℤ where
  add_comm := Int.add_comm

public instance : IsLeftCancel₀ ℕ where
  of_mul_left₀ h := Nat.mul_left_cancel (Nat.pos_of_ne_zero h)
public instance : IsRightCancel₀ ℕ := inferInstance
public instance : IsLeftCancel₀ ℤ where
  of_mul_left₀ h := (Int.mul_eq_mul_left_iff h).mp
public instance : IsRightCancel₀ ℤ := inferInstance

public instance : IsLeftAddCancel ℕ where
  of_add_left := Nat.add_left_cancel
public instance : IsRightAddCancel ℕ := inferInstance
public instance : IsLeftAddCancel ℤ where
  of_add_left := Int.add_left_cancel
public instance : IsRightCancel₀ ℤ := inferInstance

end Basic

section Theorems

public instance [Mul α] (a: α) : IsCommAt a a where
  mul_comm := rfl
public instance [Add α] (a: α) : IsAddCommAt a a where
  add_comm := rfl
public instance [Mul α] (a b: α) [IsCommAt a b] : IsAddCommAt (AddOfMul.mk a) (AddOfMul.mk b) where
  add_comm := mul_comm a b
public instance [Add α] (a b: α) [IsAddCommAt a b] : IsCommAt (MulOfAdd.mk a) (MulOfAdd.mk b) where
  mul_comm := add_comm a b

end Theorems
