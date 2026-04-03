import LeanMath.Algebra.AddMonoidWithOne.Defs
import LeanMath.Algebra.Monoid.Set

structure AddSubMonoidWithOne (α: Type*) [Add α] [Zero α] [One α] extends AddSubMonoid α, SubOne α where

instance [Add α] [Zero α] [One α] : SetLike (AddSubMonoidWithOne α) α where
instance [Add α] [Zero α] [One α] : IsMemAdd (AddSubMonoidWithOne α) α where
instance [Add α] [Zero α] [One α] : IsMemZero (AddSubMonoidWithOne α) α where
instance [Add α] [Zero α] [One α] : IsMemOne (AddSubMonoidWithOne α) α where

section

variable (s: S) [SetLike S α] [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] [IsMemAdd S α] [IsMemZero S α] [IsMemOne S α]

def mem_natCast (n: ℕ) : (n: α) ∈ s := by
  rw [natCast_eq_nsmul_one]
  apply mem_nsmul
  apply mem_one

instance : NatCast s where
  natCast n := {
    val := n
    property := mem_natCast s _
  }

instance : IsAddMonoidWithOne s where
  natCast_zero := by
    apply Subtype.val_inj
    apply natCast_zero
  natCast_one := by
    apply Subtype.val_inj
    apply natCast_one
  natCast_succ _ := by
    apply Subtype.val_inj
    apply natCast_succ

end

namespace AddSubMonoidWithOne

variable [Add α] [Add β] [One α] [One β] [Zero α] [Zero β]

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| one : Closure U 1
| add ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a + b)

def closure (U: Set α) : AddSubMonoidWithOne α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_add := Closure.add

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a
  apply Closure.of

def of_mem_closure [SetLike S α] [IsMemAdd S α] [IsMemOne S α] [IsMemZero S α] (U: Set α) (s: S)
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

instance : Top (AddSubMonoidWithOne α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_add _ _ _ _ := True.intro
  }

def mem_top (a: α) : a ∈ (⊤: AddSubMonoidWithOne α) := True.intro
def sub_top (a: AddSubMonoidWithOne α) : a ⊆ ⊤ := fun _ _ => True.intro

end AddSubMonoidWithOne

section

variable [AddMonoidWithOneOps α] [AddMonoidWithOneOps β] [IsAddMonoidWithOne α] [IsAddMonoidWithOne β]

namespace AddSubMonoidWithOne

instance : Bot (AddSubMonoidWithOne α) where
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
  }

def bot_sub (a: AddSubMonoidWithOne α) : ⊥ ⊆ a := by
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

def preimage (f: α →+₁ β) (U: AddSubMonoidWithOne β) : AddSubMonoidWithOne α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_one := MemOne.preimage f _
  mem_add := MemAdd.preimage f _

def image (f: α →+₁ β) (U: AddSubMonoidWithOne α) : AddSubMonoidWithOne β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_one := MemOne.image f _
  mem_add := MemAdd.image f _

def kernel (f: α →+₁ β) : AddSubMonoidWithOne α := preimage f ⊥

end AddSubMonoidWithOne

end
