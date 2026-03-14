import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.AddGroupWithOne.Set
import LeanMath.Algebra.Semiring.Set

structure Subring (α: Type*) [Add α] [Mul α] [Neg α] [Zero α] [One α] extends AddSubgroupWithOne α, Subsemiring α where

instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : SetLike (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemMul (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemAdd (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemNeg (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemOne (Subring α) α where
instance [Add α] [Mul α] [Neg α] [Zero α] [One α] : IsMemZero (Subring α) α where

section

variable (s: S) [SetLike S α] [RingOps α] [IsRing α] [IsMemAdd S α] [IsMemMul S α] [IsMemNeg S α] [IsMemOne S α] [IsMemZero S α]

instance : RingOps s where

instance : IsRing s where

end

namespace Subring

variable [Mul α] [Mul β] [Add α] [Add β] [Neg α] [Neg β] [One α] [One β] [Zero α] [Zero β]

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| one : Closure U 1
| neg {a: α} : Closure U a -> Closure U (-a)
| add ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a + b)
| mul ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a * b)

def closure (U: Set α) : Subring α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_neg := Closure.neg
  mem_add := Closure.add
  mem_mul := Closure.mul

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a
  apply Closure.of

def of_mem_closure [SetLike S α] [IsMemMul S α] [IsMemAdd S α] [IsMemNeg S α] [IsMemOne S α] [IsMemZero S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | one => apply mem_one
  | neg a iha =>
    apply mem_neg <;> assumption
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | mul a b iha ihb =>
    apply mem_mul <;> assumption

instance : Top (Subring α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_neg _ := True.intro
    mem_add _ _ _ _ := True.intro
    mem_mul _ _ _ _ := True.intro
  }

def mem_top (a: α) : a ∈ (⊤: Subring α) := True.intro
def sub_top (a: Subring α) : a ⊆ ⊤ := fun _ _ => True.intro

end Subring

section

variable [RingOps α] [RingOps β] [IsRing α] [IsRing β]

namespace Subring

instance : Bot (Subring α) where
  bot := {
    toSet := Set.range Int.cast
    mem_zero := by simp; exists 0; rw [intCast_zero]
    mem_one := by simp; exists 1; rw [intCast_one]
    mem_add := by
      rintro _ _ ha hb
      simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←intCast_add]
      apply Set.mem_range'
    mem_neg := by
      rintro _ ha
      simp at ha
      obtain ⟨a, rfl⟩ := ha
      rw [←intCast_neg]
      apply Set.mem_range'
    mem_mul := by
      rintro _ _ ha hb
      simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←intCast_mul]
      apply Set.mem_range'
  }

def bot_sub (a: Subring α) : ⊥ ⊆ a := by
  rintro x h
  replace h: x ∈ Set.range Int.cast := h
  simp at h; obtain ⟨n, rfl⟩ := h
  apply mem_intCast a

@[simp] def closure_bot_eq_bot : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

def preimage (f: α →+* β) (U: Subring β) : Subring α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_one := MemOne.preimage f _
  mem_neg := MemNeg.preimage f _
  mem_add := MemAdd.preimage f _
  mem_mul := MemMul.preimage f _

def image (f: α →+* β) (U: Subring α) : Subring β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_one := MemOne.image f _
  mem_neg := MemNeg.image f _
  mem_add := MemAdd.image f _
  mem_mul := MemMul.image f _

def kernel (f: α →+* β) : Subring α := preimage f ⊥

end Subring

end
