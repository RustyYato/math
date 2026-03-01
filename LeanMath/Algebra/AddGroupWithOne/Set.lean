import LeanMath.Algebra.AddGroupWithOne.Defs
import LeanMath.Algebra.AddMonoidWithOne.Set
import LeanMath.Algebra.Group.Set

structure AddSubgroupWithOne (α: Type*) [Add α] [Neg α] [Zero α] [One α] extends AddSubgroup α, AddSubMonoidWithOne α where

instance [Add α] [Neg α] [Zero α] [One α] : SetLike (AddSubgroupWithOne α) α where
instance [Add α] [Neg α] [Zero α] [One α] : IsMemAdd (AddSubgroupWithOne α) α where
instance [Add α] [Neg α] [Zero α] [One α] : IsMemNeg (AddSubgroupWithOne α) α where
instance [Add α] [Neg α] [Zero α] [One α] : IsMemZero (AddSubgroupWithOne α) α where
instance [Add α] [Neg α] [Zero α] [One α] : IsMemOne (AddSubgroupWithOne α) α where

section

variable (s: S) [SetLike S α] [AddGroupWithOneOps α] [IsAddGroupWithOne α] [IsMemAdd S α] [IsMemNeg S α] [IsMemZero S α] [IsMemOne S α]

def mem_intCast (n: ℤ) : (n: α) ∈ s := by
  rw [intCast_eq_zsmul_one]
  apply mem_zsmul
  apply mem_one

instance : IntCast s where
  intCast n := {
    val := n
    property := mem_intCast s _
  }

instance : IsAddGroupWithOne s where
  intCast_ofNat _ := by
    apply Subtype.val_inj
    apply intCast_ofNat
  intCast_negSucc _ := by
    apply Subtype.val_inj
    apply intCast_negSucc

end

namespace AddSubgroupWithOne

variable [Add α] [Add β] [Neg α] [Neg β] [One α] [One β] [Zero α] [Zero β]

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| one : Closure U 1
| neg {a: α} : Closure U a -> Closure U (-a)
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)

def closure (U: Set α) : AddSubgroupWithOne α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_neg := Closure.neg
  mem_add := Closure.add

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a
  apply Closure.of

def of_mem_closure [SetLike S α] [IsMemAdd S α] [IsMemNeg S α] [IsMemOne S α] [IsMemZero S α] (U: Set α) (s: S)
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

instance : Top (AddSubgroupWithOne α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_neg _ := True.intro
    mem_add _ _ := True.intro
  }

def mem_top (a: α) : a ∈ (⊤: AddSubgroupWithOne α) := True.intro
def sub_top (a: AddSubgroupWithOne α) : a ⊆ ⊤ := fun _ _ => True.intro

end AddSubgroupWithOne

section

variable [AddGroupWithOneOps α] [AddGroupWithOneOps β] [IsAddGroupWithOne α] [IsAddGroupWithOne β]

namespace AddSubgroupWithOne

instance : Bot (AddSubgroupWithOne α) where
  bot := {
    toSet := Set.range Int.cast
    mem_zero := by simp; exists 0; rw [intCast_zero]
    mem_one := by simp; exists 1; rw [intCast_one]
    mem_neg := by
      rintro _ ha
      simp at ha
      obtain ⟨a, rfl⟩ := ha
      rw [←intCast_neg]
      apply Set.mem_range'
    mem_add := by
      rintro _ _ ha hb
      simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←intCast_add]
      apply Set.mem_range'
  }

def bot_sub (a: AddSubgroupWithOne α) : ⊥ ⊆ a := by
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

def preimage (f: α →+₁ β) (U: AddSubgroupWithOne β) : AddSubgroupWithOne α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_one := MemOne.preimage f _
  mem_neg := MemNeg.preimage f _
  mem_add := MemAdd.preimage f _

def image (f: α →+₁ β) (U: AddSubgroupWithOne α) : AddSubgroupWithOne β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_one := MemOne.image f _
  mem_neg := MemNeg.image f _
  mem_add := MemAdd.image f _

def kernel (f: α →+₁ β) : AddSubgroupWithOne α := preimage f ⊥

end AddSubgroupWithOne

end
