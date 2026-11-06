module

public import Math.Algebra.AddMonoidWithOne.Set.Defs
public import Math.Algebra.Semiring.Defs

namespace Math

public structure Subsemiring (α: Type*) [Zero α] [One α] [Add α] [Mul α] extends AddSubmonoidWithOne α, Submonoid α where

public instance [Zero α] [One α] [Add α] [Mul α] : SetLike (Subsemiring α) α where
public instance [Zero α] [One α] [Add α] [Mul α] : IsMemZero (Subsemiring α) α where
public instance [Zero α] [One α] [Add α] [Mul α] : IsMemOne (Subsemiring α) α where
public instance [Zero α] [One α] [Add α] [Mul α] : IsMemAdd (Subsemiring α) α where
public instance [Zero α] [One α] [Add α] [Mul α] : IsMemMul (Subsemiring α) α where

namespace Subsemiring

variable [Zero α] [One α] [Add α] [Mul α]

inductive Closure [Add α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| zero : Closure U 0
| one : Closure U 1
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a * b)

public def closure (U: Set α) : Subsemiring α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_add := Closure.add
  mem_mul := Closure.mul

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α] [IsMemMul S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | one => apply mem_one
  | add => apply mem_add <;> assumption
  | mul => apply mem_mul <;> assumption

public instance : Top (Subsemiring α) where
   top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_add _ _ := True.intro
    mem_mul _ _ := True.intro
   }

public instance {α: Type*} [SemiringOps α] [IsSemiring α] : Bot (Subsemiring α) where
   bot := {
    toSet := Set.range Nat.cast
    mem_zero := by
      show 0 ∈ _
      rw [←natCast_zero]
      apply Set.mem_range'
    mem_one := by
      show 1 ∈ _
      rw [←natCast_one]
      apply Set.mem_range'
    mem_add {a b} := by
      intro ha hb; simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←natCast_add]; apply Set.mem_range'
    mem_mul {a b} := by
      intro ha hb; simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←natCast_mul]; apply Set.mem_range'
   }

public theorem bot_sub {α: Type*} [SemiringOps α] [IsSemiring α] (a: Subsemiring α) : ⊥ ⊆ a := by
  intro x h
  obtain ⟨n, rfl⟩  := Set.mem_range.mp h
  apply mem_natCast _ a
public theorem sub_top (a: Subsemiring α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α] [IsMemMul S α]

@[expose] public def of (s: S) : Subsemiring α where
  toSet := s
  mem_zero := mem_zero s
  mem_one := mem_one s
  mem_add := mem_add s
  mem_mul := mem_mul s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : Subsemiring α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_one := MemOne.copy' hu
  mem_add := MemAdd.copy' hu
  mem_mul := MemMul.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

variable [Zero β] [One β] [Add β] [Mul β] [Funlike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

@[expose] public def preimage (f: F) (s: Subsemiring β) : Subsemiring α where
  toSet := Set.preimage f s
  mem_zero := MemZero.preimage f s
  mem_one := MemOne.preimage f s
  mem_add := MemAdd.preimage f s
  mem_mul := MemMul.preimage f s
@[expose] public def image (f: F) (s: Subsemiring α) : Subsemiring β where
  toSet := Set.image f s
  mem_zero := MemZero.image f s
  mem_one := MemOne.image f s
  mem_add := MemAdd.image f s
  mem_mul := MemMul.image f s

@[simp] public theorem mem_preimage {f: F} {s: Subsemiring β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Subsemiring α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end Subsemiring
