module

public import Math.Algebra.Semiring.Defs.Basic
public import Math.Algebra.Monoid.Set.Defs

namespace Math

@[expose] section Defs

public def MemMulLeft [SetLike S α] [Mul α] (s: S) : Prop :=
  ∀k, ∀{a}, a ∈ s -> k * a ∈ s
public def MemMulRight [SetLike S α] [Mul α] (s: S) : Prop :=
  ∀k, ∀{a}, a ∈ s -> a * k ∈ s

public class IsMemMulLeft (S α: Type*) [SetLike S α] [Mul α] : Prop where
  mem_mul_left (s: S) : MemMulLeft s := by intro s; exact s.mem_mul_left

public class IsMemMulRight (S α: Type*) [SetLike S α] [Mul α] : Prop where
  mem_mul_right (s: S) : MemMulRight s := by intro s; exact s.mem_mul_right

export IsMemMulLeft (mem_mul_left)
export IsMemMulRight (mem_mul_right)

public structure IdealLeft (α: Type*) [Zero α] [Add α] [Mul α] extends AddSubmonoid α where
  protected mem_mul_left: MemMulLeft toSet

public structure IdealRight (α: Type*) [Zero α] [Add α] [Mul α] extends AddSubmonoid α where
  protected mem_mul_right: MemMulRight toSet

public structure Ideal (α: Type*) [Zero α] [Add α] [Mul α] extends IdealLeft α, IdealRight α where

end Defs

section Instances

variable [Zero α] [Add α] [Mul α]

public instance : SetLike (IdealLeft α) α where
public instance : SetLike (IdealRight α) α where
public instance : SetLike (Ideal α) α where

public instance : IsMemZero (IdealLeft α) α where
public instance : IsMemZero (IdealRight α) α where
public instance : IsMemZero (Ideal α) α where
public instance : IsMemAdd (IdealLeft α) α where
public instance : IsMemAdd (IdealRight α) α where
public instance : IsMemAdd (Ideal α) α where
public instance : IsMemMulLeft (IdealLeft α) α where
public instance : IsMemMulRight (IdealRight α) α where
public instance : IsMemMulLeft (Ideal α) α where
public instance : IsMemMulRight (Ideal α) α where

end Instances

namespace MemMulLeft

variable [Mul α] [Mul β] [SetLike S α] [IsMemMulLeft S α]

public theorem copy (u: Set α) (h: ∃s: S, u = s) : MemMulLeft u := by
  obtain ⟨s, rfl⟩ := h
  exact mem_mul_left s

public theorem copy'
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemMulLeft u:= by
  intro k a ha
  apply (h _).mp
  apply mem_mul_left
  apply (h _).mpr
  assumption

end MemMulLeft

namespace MemMulRight

variable [Mul α] [Mul β] [SetLike S α] [IsMemMulRight S α]

public theorem copy (u: Set α) (h: ∃s: S, u = s) : MemMulRight u := by
  obtain ⟨s, rfl⟩ := h
  exact mem_mul_right s

public theorem copy'
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemMulRight u:= by
  intro k a ha
  apply (h _).mp
  apply mem_mul_right
  apply (h _).mpr
  assumption

end MemMulRight

namespace IdealLeft

variable {α: Type*} [Zero α] [Add α] [Mul α]

@[ext] public theorem ext (a b: IdealLeft α) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := SetLike.ext _ _ h

inductive Closure {α: Type*} (U: Set α) [Zero α] [Add α] [Mul α] : α -> Prop where
| of : a ∈ U -> Closure U a
| zero : Closure U 0
| add : Closure U a -> Closure U b -> Closure U (a + b)
| mul_left (k: α) {a: α} : Closure U a -> Closure U (k * a)

public def closure (U: Set α) : IdealLeft α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_add := Closure.add
  mem_mul_left := Closure.mul_left

variable {S: Type*} [SetLike S α] [IsMemZero S α] [IsMemAdd S α] [IsMemMulLeft S α]

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | add => apply mem_add <;> assumption
  | mul_left => apply mem_mul_left <;> assumption

@[expose] public def of (s: S) : IdealLeft α where
  toSet := s
  mem_zero := mem_zero s
  mem_add := mem_add s
  mem_mul_left := mem_mul_left s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : IdealLeft α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_add := MemAdd.copy' hu
  mem_mul_left := MemMulLeft.copy' hu

variable {α: Type*} [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α]

public instance : Bot (IdealLeft α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add {a b} := by intro rfl rfl; rw [add_zero]; rfl
    mem_mul_left {k a} := by intro rfl; rw [mul_zero]; rfl
  }
public instance [IsNonUnitalNonAssocSemiring α] : Top (IdealLeft α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ := True.intro
    mem_mul_left {_ _} _ := True.intro
  }

public theorem bot_sub (a: IdealLeft α) : ⊥ ⊆ a := by intro x rfl; exact mem_zero a
public theorem sub_top (a: IdealLeft α) : a ⊆ ⊤ := fun _ _ => True.intro

end IdealLeft

namespace IdealRight

variable {α: Type*} [Zero α] [Add α] [Mul α]

@[ext] public theorem ext (a b: IdealRight α) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := SetLike.ext _ _ h

inductive Closure {α: Type*} (U: Set α) [Zero α] [Add α] [Mul α] : α -> Prop where
| of : a ∈ U -> Closure U a
| zero : Closure U 0
| add : Closure U a -> Closure U b -> Closure U (a + b)
| mul_right (k: α) {a: α} : Closure U a -> Closure U (a * k)

public def closure (U: Set α) : IdealRight α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_add := Closure.add
  mem_mul_right := Closure.mul_right

variable {S: Type*} [SetLike S α] [IsMemZero S α] [IsMemAdd S α] [IsMemMulRight S α]

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | add => apply mem_add <;> assumption
  | mul_right => apply mem_mul_right <;> assumption

@[expose] public def of (s: S) : IdealRight α where
  toSet := s
  mem_zero := mem_zero s
  mem_add := mem_add s
  mem_mul_right := mem_mul_right s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : IdealRight α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_add := MemAdd.copy' hu
  mem_mul_right := MemMulRight.copy' hu

variable {α: Type*} [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α]

public instance : Bot (IdealRight α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add {a b} := by intro rfl rfl; rw [add_zero]; rfl
    mem_mul_right {k a} := by intro rfl; rw [zero_mul]; rfl
  }
public instance [IsNonUnitalNonAssocSemiring α] : Top (IdealRight α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ := True.intro
    mem_mul_right {_ _} _ := True.intro
  }

public theorem bot_sub (a: IdealRight α) : ⊥ ⊆ a := by intro x rfl; exact mem_zero a
public theorem sub_top (a: IdealRight α) : a ⊆ ⊤ := fun _ _ => True.intro

end IdealRight

namespace Ideal

variable {α: Type*} [Zero α] [Add α] [Mul α]

@[ext] public theorem ext (a b: Ideal α) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := SetLike.ext _ _ h

inductive Closure {α: Type*} (U: Set α) [Zero α] [Add α] [Mul α] : α -> Prop where
| of : a ∈ U -> Closure U a
| zero : Closure U 0
| add : Closure U a -> Closure U b -> Closure U (a + b)
| mul_left (k: α) {a: α} : Closure U a -> Closure U (k * a)
| mul_right (k: α) {a: α} : Closure U a -> Closure U (a * k)

public def closure (U: Set α) : Ideal α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_add := Closure.add
  mem_mul_left := Closure.mul_left
  mem_mul_right := Closure.mul_right

variable {S: Type*} [SetLike S α] [IsMemZero S α] [IsMemAdd S α] [IsMemMulLeft S α] [IsMemMulRight S α]

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | add => apply mem_add <;> assumption
  | mul_left => apply mem_mul_left <;> assumption
  | mul_right => apply mem_mul_right <;> assumption

@[expose] public def of (s: S) : Ideal α where
  toSet := s
  mem_zero := mem_zero s
  mem_add := mem_add s
  mem_mul_left := mem_mul_left s
  mem_mul_right := mem_mul_right s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : Ideal α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_add := MemAdd.copy' hu
  mem_mul_left := MemMulLeft.copy' hu
  mem_mul_right := MemMulRight.copy' hu

variable {α: Type*} [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α]

public instance : Bot (Ideal α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add {a b} := by intro rfl rfl; rw [add_zero]; rfl
    mem_mul_left {k a} := by intro rfl; rw [mul_zero]; rfl
    mem_mul_right {k a} := by intro rfl; rw [zero_mul]; rfl
  }
public instance [IsNonUnitalNonAssocSemiring α] : Top (Ideal α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ := True.intro
    mem_mul_left {_ _} _ := True.intro
    mem_mul_right {_ _} _ := True.intro
  }

public theorem bot_sub (a: Ideal α) : ⊥ ⊆ a := by intro x rfl; exact mem_zero a
public theorem sub_top (a: Ideal α) : a ⊆ ⊤ := fun _ _ => True.intro

end Ideal
