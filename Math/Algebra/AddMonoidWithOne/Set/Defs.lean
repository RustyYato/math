module

public import Math.Data.Set.Nonempty
public import Math.Algebra.Monoid.Set.Defs
public import Math.Algebra.AddMonoidWithOne.Defs.Basic

namespace Math

public structure AddSubmonoidWithOne (α: Type*) [Zero α] [One α] [Add α] extends AddSubmonoid α where
  protected mem_one : MemOne toSet

public instance [Zero α] [One α] [Add α] : SetLike (AddSubmonoidWithOne α) α where
public instance [Zero α] [One α] [Add α] : IsMemZero (AddSubmonoidWithOne α) α where
public instance [Zero α] [One α] [Add α] : IsMemOne (AddSubmonoidWithOne α) α where
public instance [Zero α] [One α] [Add α] : IsMemAdd (AddSubmonoidWithOne α) α where

public theorem mem_natCast
  [Zero α] [One α] [Add α] [NatCast α] [IsLawfulNatCast α]
  [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α]
  (n: ℕ) (s: S) : (n: α) ∈ s := by
  induction n with
  | zero => rw [natCast_zero]; apply mem_zero
  | succ => rw [natCast_succ]; apply mem_add; assumption; apply mem_one

namespace AddSubmonoidWithOne

variable [Zero α] [One α] [Add α]

inductive Closure [Add α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| zero : Closure U 0
| one : Closure U 1
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)

public def closure (U: Set α) : AddSubmonoidWithOne α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_one := Closure.one
  mem_add := Closure.add

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | one => apply mem_one
  | add => apply mem_add <;> assumption

public instance : Top (AddSubmonoidWithOne α) where
   top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_one := True.intro
    mem_add _ _ := True.intro
   }

public instance {α: Type*} [AddMonoidOps α] [NatCast α] [One α] [IsAddMonoidWithOne α] : Bot (AddSubmonoidWithOne α) where
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
   }

public theorem bot_sub {α: Type*} [AddMonoidOps α] [NatCast α] [One α] [IsAddMonoidWithOne α] (a: AddSubmonoidWithOne α) : ⊥ ⊆ a := by
  intro x h
  obtain ⟨n, rfl⟩  := Set.mem_range.mp h
  apply mem_natCast _ a
public theorem sub_top (a: AddSubmonoidWithOne α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α]

@[expose] public def of (s: S) : AddSubmonoidWithOne α where
  toSet := s
  mem_zero := mem_zero s
  mem_one := mem_one s
  mem_add := mem_add s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : AddSubmonoidWithOne α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_one := MemOne.copy' hu
  mem_add := MemAdd.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

variable [Zero β] [One β] [Add β] [Funlike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]

@[expose] public def preimage (f: F) (s: AddSubmonoidWithOne β) : AddSubmonoidWithOne α where
  toSet := Set.preimage f s
  mem_zero := MemZero.preimage f s
  mem_one := MemOne.preimage f s
  mem_add := MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubmonoidWithOne α) : AddSubmonoidWithOne β where
  toSet := Set.image f s
  mem_zero := MemZero.image f s
  mem_one := MemOne.image f s
  mem_add := MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubmonoidWithOne β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubmonoidWithOne α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end AddSubmonoidWithOne

public instance [Zero α] [One α] [Add α] [NatCast α] [IsLawfulNatCast α]
  [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α] (s: S) : NatCast s where
  natCast n := {
    val := n
    property := mem_natCast n s
  }

public instance [Zero α] [One α] [Add α] [NatCast α] [IsLawfulNatCast α]
  [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α] (s: S) : IsLawfulNatCast s where
  natCast_zero := by ext; apply natCast_zero
  natCast_succ _ := by ext; apply natCast_succ

public instance [AddMonoidOps α] [One α] [NatCast α] [IsAddMonoidWithOne α]
  [SetLike S α] [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α] (s: S) : IsAddMonoidWithOne s where
