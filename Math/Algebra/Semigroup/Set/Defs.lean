module

public import Math.Data.Set.Defs
public import Math.Algebra.Semigroup.Defs.Basic

namespace Math

public abbrev MemMul [Mul α] [SetLike S α] (s: S) : Prop :=
  ∀{a b: α}, a ∈ s -> b ∈ s -> a * b ∈ s

public abbrev MemAdd [Add α] [SetLike S α] (s: S) : Prop :=
  ∀{a b: α}, a ∈ s -> b ∈ s -> a + b ∈ s

public class IsMemMul (S α: Type*) [SetLike S α] [Mul α] where
  mem_mul (s: S) : MemMul s := by intro s; exact s.mem_mul
public class IsMemAdd (S α: Type*) [SetLike S α] [Add α] where
  mem_add (s: S) {a b: α} : a ∈ s -> b ∈ s -> a + b ∈ s := by intro s; exact s.mem_add

export IsMemMul (mem_mul)
export IsMemAdd (mem_add)

public structure Subsemigroup (α: Type*) [Mul α] where
  toSet : Set α
  protected mem_mul : MemMul toSet
public structure AddSubsemigroup (α: Type*) [Add α] where
  toSet : Set α
  protected mem_add : MemAdd toSet

public instance [Mul α] : SetLike (Subsemigroup α) α where
public instance [Add α] : SetLike (AddSubsemigroup α) α where

public instance [Mul α] : IsMemMul (Subsemigroup α) α where
public instance [Add α] : IsMemAdd (AddSubsemigroup α) α where

namespace MemMul

public theorem copy [Mul α] [SetLike S α] [IsMemMul S α]
  (u: Set α) (h: ∃s: S, u = s) : MemMul u:= by
  obtain ⟨s, rfl⟩ := h
  exact mem_mul s

public theorem copy' [Mul α] [SetLike S α] [IsMemMul S α]
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemMul u:= by
  intro a b ha hb
  apply (h _).mp
  apply mem_mul
  apply (h _).mpr; assumption
  apply (h _).mpr; assumption

end MemMul

namespace MemAdd

public theorem copy [Add α] [SetLike S α] [IsMemAdd S α]
  (u: Set α) (h: ∃s: S, u = s) : MemAdd u:= by
  obtain ⟨s, rfl⟩ := h
  exact mem_add s

public theorem copy' [Add α] [SetLike S α] [IsMemAdd S α]
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemAdd u:= by
  intro a b ha hb
  apply (h _).mp
  apply mem_add
  apply (h _).mpr; assumption
  apply (h _).mpr; assumption

end MemAdd

namespace Subsemigroup

variable [Mul α]

inductive Closure [Mul α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a * b)

public def closure (U: Set α) : Subsemigroup α where
  toSet := { Mem := Closure U }
  mem_mul := Closure.mul

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemMul S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | mul => apply mem_mul <;> assumption

public instance : Top (Subsemigroup α) where
   top := {
    toSet := ⊤
    mem_mul _ _ := True.intro
   }

public instance : Bot (Subsemigroup α) where
   bot := {
    toSet := ⊥
    mem_mul := nofun
   }

public theorem bot_sub (a: Subsemigroup α) : ⊥ ⊆ a := nofun

public theorem sub_top (a: Subsemigroup α) : a ⊆ ⊤ := fun _ _ => True.intro

@[expose] public def of [SetLike S α] [IsMemMul S α] (s: S) : Subsemigroup α where
  toSet := s
  mem_mul := mem_mul s
@[expose] public def copy [SetLike S α] [IsMemMul S α] (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : Subsemigroup α where
  toSet := u
  mem_mul := MemMul.copy' hu

@[simp] public theorem mem_of [SetLike S α] [IsMemMul S α] {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy [SetLike S α] [IsMemMul S α] {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end Subsemigroup

namespace AddSubsemigroup

variable [Add α]

inductive Closure (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)

public def closure (U: Set α) : AddSubsemigroup α where
  toSet := { Mem := Closure U }
  mem_add := Closure.mul

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemAdd S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | mul => apply mem_add <;> assumption

public instance : Top (AddSubsemigroup α) where
   top := {
    toSet := ⊤
    mem_add _ _ := True.intro
   }

public instance : Bot (AddSubsemigroup α) where
   bot := {
    toSet := ⊥
    mem_add := nofun
   }

public theorem bot_sub (a: AddSubsemigroup α) : ⊥ ⊆ a := nofun

public theorem sub_top (a: AddSubsemigroup α) : a ⊆ ⊤ := fun _ _ => True.intro

@[expose] public def of [SetLike S α] [IsMemAdd S α] (s: S) : AddSubsemigroup α where
  toSet := s
  mem_add := mem_add s
@[expose] public def copy [SetLike S α] [IsMemAdd S α] (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : AddSubsemigroup α where
  toSet := u
  mem_add := MemAdd.copy' hu

@[simp] public theorem mem_of [SetLike S α] [IsMemAdd S α] {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy [SetLike S α] [IsMemAdd S α] {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end AddSubsemigroup

variable [SetLike S α]

attribute [local irreducible] MulOfAdd in
public instance : SetLike (MulOfAdd S) (MulOfAdd α) where
  coeSet s := (Set.coe s.get).preimage MulOfAdd.get
  coeInj := by
    intro a b h; dsimp at h
    induction a with | _ a =>
    induction b with | _ b =>
    dsimp at h; congr
    apply Set.coe_inj
    ext i
    show (MulOfAdd.mk i ∈ Set.preimage MulOfAdd.get a) ↔ (MulOfAdd.mk i ∈ Set.preimage MulOfAdd.get b)
    rw [h]

attribute [local irreducible] AddOfMul in
public instance : SetLike (AddOfMul S) (AddOfMul α) where
  coeSet s := (Set.coe s.get).preimage AddOfMul.get
  coeInj := by
    intro a b h; dsimp at h
    induction a with | _ a =>
    induction b with | _ b =>
    dsimp at h; congr
    apply Set.coe_inj
    ext i
    show (AddOfMul.mk i ∈ Set.preimage AddOfMul.get a) ↔ (AddOfMul.mk i ∈ Set.preimage AddOfMul.get b)
    rw [h]

public instance [Add α] [IsMemAdd S α] : IsMemMul (MulOfAdd S) (MulOfAdd α) where
  mem_mul := mem_add (S := S) (α := α)
public instance [Mul α] [IsMemMul S α] : IsMemAdd (AddOfMul S) (AddOfMul α) where
  mem_add := mem_mul (S := S) (α := α)

public instance [Mul α] [IsMemMul S α] (s: S) : Mul s where
  mul a b := {
    val := a.val * b.val
    property := mem_mul s a.property b.property
  }

public instance [Add α] [IsMemAdd S α] (s: S) : Add s where
  add a b := {
    val := a.val + b.val
    property := mem_add s a.property b.property
  }

@[simp] public theorem subtype_mul [Mul α] [IsMemMul S α] {s: S} (a b: (s: Type _)) : (a * b).val = a.val * b.val := rfl
@[simp] public theorem subtype_add [Add α] [IsMemAdd S α] {s: S} (a b: (s: Type _)) : (a + b).val = a.val + b.val := rfl

public instance [Mul α] [IsMemMul S α] [IsSemigroup α] (s: S) : IsSemigroup s where
  mul_assoc a b c := by ext; apply mul_assoc
public instance [Mul α] [IsMemMul S α] [IsComm α] (s: S) : IsComm s where
  mul_comm a b := by ext; apply mul_comm

public instance [Add α] [IsMemAdd S α] [IsAddSemigroup α] (s: S) : IsAddSemigroup s where
  add_assoc a b c := by ext; apply add_assoc
public instance [Add α] [IsMemAdd S α] [IsAddComm α] (s: S) : IsAddComm s where
  add_comm a b := by ext; apply add_comm

public instance [Mul α] [IsMemMul S α] [IsLeftCancel α] (s: S) : IsLeftCancel s where
  of_mul_left {k a b} h := by
    ext; apply of_mul_left (k := k.val)
    exact congrArg Subtype.val h
public instance [Mul α] [IsMemMul S α] [IsRightCancel α] (s: S) : IsRightCancel s where
  of_mul_right {k a b} h := by
    ext; apply of_mul_right (k := k.val)
    exact congrArg Subtype.val h
public instance [Add α] [IsMemAdd S α] [IsLeftAddCancel α] (s: S) : IsLeftAddCancel s where
  of_add_left {k a b} h := by
    ext; apply of_add_left (k := k.val)
    exact congrArg Subtype.val h
public instance [Add α] [IsMemAdd S α] [IsRightAddCancel α] (s: S) : IsRightAddCancel s where
  of_add_right {k a b} h := by
    ext; apply of_add_right (k := k.val)
    exact congrArg Subtype.val h
