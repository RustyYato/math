module

public import Math.Data.Set.Nonempty
public import Math.Algebra.AddMonoidWithOne.Set.Defs
public import Math.Algebra.Group.Set.Defs
public import Math.Algebra.AddGroupWithOne.Defs

namespace Math

public structure AddSubgroupWithOne (α: Type*) [Zero α] [One α] [Neg α] [Add α] extends
  AddSubgroup α, AddSubmonoidWithOne α where

public instance [Zero α] [One α] [Neg α] [Add α] : SetLike (AddSubgroupWithOne α) α where
public instance [Zero α] [One α] [Neg α] [Add α] : IsMemZero (AddSubgroupWithOne α) α where
public instance [Zero α] [One α] [Neg α] [Add α] : IsMemOne (AddSubgroupWithOne α) α where
public instance [Zero α] [One α] [Neg α] [Add α] : IsMemNeg (AddSubgroupWithOne α) α where
public instance [Zero α] [One α] [Neg α] [Add α] : IsMemAdd (AddSubgroupWithOne α) α where

public theorem mem_intCast
  [AddGroupOps α] [NatCast α] [IntCast α] [One α] [IsAddGroupWithOne α]
  [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemNeg S α] [IsMemAdd S α]
  (n: ℤ) (s: S) : (n: α) ∈ s := by
  cases n with
  | ofNat n => dsimp; rw [intCast_ofNat]; apply mem_natCast
  | negSucc n => rw [intCast_negSucc]; apply mem_neg; apply mem_natCast

namespace AddSubgroupWithOne

variable [Zero α] [One α] [Neg α] [Add α]

inductive Closure [Add α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| zero : Closure U 0
| one : Closure U 1
| neg {a: α} : Closure U a -> Closure U (-a)
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)

public def closure (U: Set α) : AddSubgroupWithOne α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_neg := Closure.neg
  mem_add := Closure.add

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemNeg S α] [IsMemAdd S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | one => apply mem_one
  | neg => apply mem_neg <;> assumption
  | add => apply mem_add <;> assumption

public instance : Top (AddSubgroupWithOne α) where
   top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_neg _ := True.intro
    mem_add _ _ := True.intro
   }

public instance {α: Type*} [AddGroupOps α] [NatCast α] [IntCast α] [One α] [IsAddGroupWithOne α] : Bot (AddSubgroupWithOne α) where
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
   }

public theorem bot_sub {α: Type*} [AddGroupOps α] [NatCast α] [IntCast α] [One α] [IsAddGroupWithOne α] (a: AddSubgroupWithOne α) : ⊥ ⊆ a := by
  intro x h
  obtain ⟨n, rfl⟩  := Set.mem_range.mp h
  apply mem_intCast _ a
public theorem sub_top (a: AddSubgroupWithOne α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemNeg S α] [IsMemAdd S α]

@[expose] public def of (s: S) : AddSubgroupWithOne α where
  toSet := s
  mem_zero := mem_zero s
  mem_one := mem_one s
  mem_neg := mem_neg s
  mem_add := mem_add s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : AddSubgroupWithOne α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_one := MemOne.copy' hu
  mem_neg := MemNeg.copy' hu
  mem_add := MemAdd.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

variable {α β: Type*} [AddGroupOps α] [One α] [IsAddGroup α] [AddGroupOps β] [One β] [IsAddGroup β]
  [Funlike F α β] [IsAddHom F α β] [IsZeroHom F α β] [IsOneHom F α β]

@[expose] public def preimage (f: F) (s: AddSubgroupWithOne β) : AddSubgroupWithOne α where
  toSet := Set.preimage f s
  mem_zero := MemZero.preimage f s
  mem_one := MemOne.preimage f s
  mem_neg := MemNeg.preimage f s
  mem_add := MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubgroupWithOne α) : AddSubgroupWithOne β where
  toSet := Set.image f s
  mem_zero := MemZero.image f s
  mem_one := MemOne.image f s
  mem_neg := MemNeg.image f s
  mem_add := MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubgroupWithOne β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubgroupWithOne α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end AddSubgroupWithOne
