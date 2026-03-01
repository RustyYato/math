import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.AddMonoidWithOne.Set

structure Subsemiring (α: Type*) [Add α] [Mul α] [Zero α] [One α] extends AddSubMonoidWithOne α, SubMonoid α where

instance [Add α] [Mul α] [Zero α] [One α] : SetLike (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemMul (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemAdd (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemOne (Subsemiring α) α where
instance [Add α] [Mul α] [Zero α] [One α] : IsMemZero (Subsemiring α) α where

section

section

variable (s: S) [SetLike S α] [Add α] [Mul α] [IsMemAdd S α] [IsMemMul S α]

instance [IsLeftDistrib α] : IsLeftDistrib s where
  mul_add _ _ _ := by
    apply Subtype.val_inj
    apply mul_add

instance [IsRightDistrib α] : IsRightDistrib s where
  add_mul _ _ _ := by
    apply Subtype.val_inj
    apply add_mul

end

variable (s: S) [SetLike S α] [SemiringOps α] [IsSemiring α] [IsMemAdd S α] [IsMemMul S α] [IsMemOne S α] [IsMemZero S α]

instance : IsSemiring s where

end

namespace Subsemiring

variable [Mul α] [Mul β] [Add α] [Add β] [One α] [One β] [Zero α] [Zero β]

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| one : Closure U 1
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a * b)

def closure (U: Set α) : Subsemiring α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_add := Closure.add
  mem_mul := Closure.mul

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a
  apply Closure.of

def of_mem_closure [SetLike S α] [IsMemMul S α] [IsMemAdd S α] [IsMemOne S α] [IsMemZero S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | one => apply mem_one
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | mul a b iha ihb =>
    apply mem_mul <;> assumption

instance : Top (Subsemiring α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_add _ _ := True.intro
    mem_mul _ _ := True.intro
  }

def mem_top (a: α) : a ∈ (⊤: Subsemiring α) := True.intro
def sub_top (a: Subsemiring α) : a ⊆ ⊤ := fun _ _ => True.intro

end Subsemiring

section

variable [SemiringOps α] [SemiringOps β] [IsSemiring α] [IsSemiring β]

namespace Subsemiring

instance : Bot (Subsemiring α) where
  bot := {
    toSet := Set.range Nat.cast
    mem_zero := by simp; exists 0; rw [natCast_zero]
    mem_one := by simp; exists 1; rw [natCast_one]
    mem_add := by
      rintro _ _ ha hb
      simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←natCast_add]
      apply Set.mem_range'
    mem_mul := by
      rintro _ _ ha hb
      simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←natCast_mul]
      apply Set.mem_range'
  }

def bot_sub (a: Subsemiring α) : ⊥ ⊆ a := by
  rintro x h
  replace h: x ∈ Set.range Nat.cast := h
  simp at h; obtain ⟨n, rfl⟩ := h
  apply mem_natCast a

@[simp] def closure_bot_eq_bot : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

def preimage (f: α →+* β) (U: Subsemiring β) : Subsemiring α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_one := MemOne.preimage f _
  mem_add := MemAdd.preimage f _
  mem_mul := MemMul.preimage f _

def image (f: α →+* β) (U: Subsemiring α) : Subsemiring β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_one := MemOne.image f _
  mem_add := MemAdd.image f _
  mem_mul := MemMul.image f _

def kernel (f: α →+* β) : Subsemiring α := preimage f ⊥

end Subsemiring

end
