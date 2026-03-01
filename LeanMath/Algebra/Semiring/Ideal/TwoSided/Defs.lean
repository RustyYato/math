import LeanMath.Algebra.Semiring.Set
import LeanMath.Algebra.Semiring.Ideal.Defs

structure Ideal (α: Type*) [SemiringOps α] [IsSemiring α] extends AddSubMonoid α, SubLeftMul α, SubRightMul α, SubZero α where

variable [SemiringOps α] [SemiringOps β] [IsSemiring α] [IsSemiring β]

instance : SetLike (Ideal α) α where
instance : IsMemAdd (Ideal α) α where
instance : IsMemLeftMul (Ideal α) α where
instance : IsMemRightMul (Ideal α) α where
instance : IsMemZero (Ideal α) α where

namespace Ideal

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)
| mul_left {a: α} (k: α) : Closure U a -> Closure U (k * a)
| mul_right {a: α} (k: α) : Closure U a -> Closure U (a * k)

def closure (U: Set α) : Ideal α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_add := Closure.add
  mem_left_mul := Closure.mul_left
  mem_right_mul := Closure.mul_right

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a
  apply Closure.of

def of_mem_closure [SetLike S α] [IsMemLeftMul S α] [IsMemRightMul S α] [IsMemAdd S α] [IsMemZero S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | mul_left a iha =>
    apply mem_left_mul <;> assumption
  | mul_right a iha =>
    apply mem_right_mul <;> assumption

instance : Top (Ideal α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ := True.intro
    mem_left_mul _ _ := True.intro
    mem_right_mul _ _ := True.intro
  }

instance : Bot (Ideal α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_left_mul := by
      rintro x _ rfl
      rw [mul_zero]; rfl
    mem_right_mul := by
      rintro x _ rfl
      rw [zero_mul]; rfl
  }

def mem_top (a: α) : a ∈ (⊤: Ideal α) := True.intro
def sub_top (a: Ideal α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub (a: Ideal α) : ⊥ ⊆ a := by
  rintro x rfl
  apply mem_zero a

@[simp] def closure_bot_eq_bot : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

def preimage (f: RingHom α β) (U: Ideal β) : Ideal α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_add := MemAdd.preimage f _
  mem_left_mul := MemLeftMul.preimage f _
  mem_right_mul := MemRightMul.preimage f _

def kernel (f: α →+* β) : Ideal α := preimage f ⊥

end Ideal
