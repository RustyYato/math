module

public import Math.Algebra.AddGroupWithOne.Set.Defs
public import Math.Algebra.Semiring.Set.Defs
public import Math.Algebra.Ring.Defs.Basic

import Math.Algebra.Ring.Defs.Lemmas

namespace Math

public structure Subring (α: Type*) [Zero α] [One α] [Neg α] [Add α] [Mul α] extends AddSubgroupWithOne α, Subsemiring α where

public instance [Zero α] [One α] [Neg α] [Add α] [Mul α] : SetLike (Subring α) α where
public instance [Zero α] [One α] [Neg α] [Add α] [Mul α] : IsMemZero (Subring α) α where
public instance [Zero α] [One α] [Neg α] [Add α] [Mul α] : IsMemOne (Subring α) α where
public instance [Zero α] [One α] [Neg α] [Add α] [Mul α] : IsMemNeg (Subring α) α where
public instance [Zero α] [One α] [Neg α] [Add α] [Mul α] : IsMemAdd (Subring α) α where
public instance [Zero α] [One α] [Neg α] [Add α] [Mul α] : IsMemMul (Subring α) α where

namespace Subring

variable [Zero α] [One α] [Neg α] [Add α] [Mul α]

inductive Closure [Add α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| zero : Closure U 0
| one : Closure U 1
| neg {a: α} : Closure U a -> Closure U (-a)
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a * b)

public def closure (U: Set α) : Subring α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_neg := Closure.neg
  mem_add := Closure.add
  mem_mul := Closure.mul

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemNeg S α] [IsMemAdd S α] [IsMemMul S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | one => apply mem_one
  | neg => apply mem_neg <;> assumption
  | add => apply mem_add <;> assumption
  | mul => apply mem_mul <;> assumption

public instance : Top (Subring α) where
   top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_neg _ := True.intro
    mem_add _ _ := True.intro
    mem_mul _ _ := True.intro
   }

public instance {α: Type*} [RingOps α] [IsRing α] : Bot (Subring α) where
   bot := {
    toSet := Set.range Int.cast
    mem_zero := by
      show 0 ∈ _
      rw [←intCast_zero]
      apply Set.mem_range'
    mem_one := by
      show 1 ∈ _
      rw [←intCast_one]
      apply Set.mem_range'
    mem_neg {a} := by
      intro ha; simp at ha
      obtain ⟨a, rfl⟩ := ha
      rw [←intCast_neg]; apply Set.mem_range'
    mem_add {a b} := by
      intro ha hb; simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←intCast_add]; apply Set.mem_range'
    mem_mul {a b} := by
      intro ha hb; simp at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←intCast_mul]; apply Set.mem_range'
   }

public theorem bot_sub {α: Type*} [RingOps α] [IsRing α] (a: Subring α) : ⊥ ⊆ a := by
  intro x h
  obtain ⟨n, rfl⟩  := Set.mem_range.mp h
  apply mem_intCast _ a
public theorem sub_top (a: Subring α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemNeg S α] [IsMemAdd S α] [IsMemMul S α]

@[expose] public def of (s: S) : Subring α where
  toSet := s
  mem_zero := mem_zero s
  mem_one := mem_one s
  mem_neg := mem_neg s
  mem_add := mem_add s
  mem_mul := mem_mul s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : Subring α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_one := MemOne.copy' hu
  mem_neg := MemNeg.copy' hu
  mem_add := MemAdd.copy' hu
  mem_mul := MemMul.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

end Subring

variable {S α: Type*} [SetLike S α]

public instance
  [AddGroupOps α] [IsAddGroup α]
  [Mul α] [IsNonUnitalNonAssocRing α]
  [IsMemZero S α] [IsMemAdd S α]
  [IsMemNeg S α] [IsMemMul S α]
  (s: S) : IsNonUnitalNonAssocRing s where

public instance
  [AddGroupOps α] [IsAddGroup α]
  [Mul α] [IsNonUnitalRing α]
  [IsMemZero S α] [IsMemAdd S α]
  [IsMemNeg S α] [IsMemMul S α]
  (s: S) : IsNonUnitalRing s where

public instance
  [AddGroupOps α] [One α] [NatCast α] [IntCast α] [IsAddGroupWithOne α]
  [Mul α] [IsNonAssocRing α]
  [IsMemZero S α] [IsMemAdd S α] [IsMemNeg S α]
  [IsMemOne S α] [IsMemMul S α]
  (s: S) : IsNonAssocRing s where

public instance
  [RingOps α] [IsRing α]
  [IsMemZero S α] [IsMemAdd S α] [IsMemNeg S α]
  [IsMemOne S α] [IsMemMul S α]
  (s: S) : RingOps s := instRingOps

public instance
  [RingOps α] [IsRing α]
  [IsMemZero S α] [IsMemAdd S α] [IsMemNeg S α]
  [IsMemOne S α] [IsMemMul S α]
  (s: S) : IsRing s where
