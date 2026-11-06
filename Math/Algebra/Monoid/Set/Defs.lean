module

public import Math.Data.Set.Nonempty
public import Math.Algebra.Semigroup.Set.Defs
public import Math.Algebra.Monoid.Defs

namespace Math

public abbrev MemOne [One α] [SetLike S α] (s: S) : Prop :=
  1 ∈ s

public abbrev MemZero [Zero α] [SetLike S α] (s: S) : Prop :=
  0 ∈ s

public class IsMemOne (S α: Type*) [SetLike S α] [One α] where
  mem_one (s: S) : MemOne s := by intro s; exact s.mem_one
public class IsMemZero (S α: Type*) [SetLike S α] [Zero α] where
  mem_zero (s: S) : MemZero s := by intro s; exact s.mem_zero

export IsMemOne (mem_one)
export IsMemZero (mem_zero)

public instance [Zero α] [SetLike S α] [IsMemZero S α] (s: S) : Set.Nonempty (s: Set α) := ⟨_, mem_zero s⟩
public instance [One α] [SetLike S α] [IsMemOne S α] (s: S) : Set.Nonempty (s: Set α) := ⟨_, mem_one s⟩

public structure Submonoid (α: Type*) [One α] [Mul α] extends Subsemigroup α where
  protected mem_one : MemOne toSet
public structure AddSubmonoid (α: Type*) [Zero α] [Add α] extends AddSubsemigroup α where
  protected mem_zero : MemZero toSet

public instance [One α] [Mul α] : SetLike (Submonoid α) α where
public instance [Zero α] [Add α] : SetLike (AddSubmonoid α) α where

public instance [One α] [Mul α] : IsMemOne (Submonoid α) α where
public instance [One α] [Mul α] : IsMemMul (Submonoid α) α where
public instance [Zero α] [Add α] : IsMemZero (AddSubmonoid α) α where
public instance [Zero α] [Add α] : IsMemAdd (AddSubmonoid α) α where

namespace MemOne

public theorem preimage
  [One α] [One β] [Funlike F α β] [IsOneHom F α β]
  [SetLike S β] [IsMemOne S β] (f: F) (s: S) : MemOne (Set.preimage f s) := by
  show f 1 ∈ s
  rw [map_one]
  apply mem_one

public theorem image
  [One α] [One β] [Funlike F α β] [IsOneHom F α β]
  [SetLike S α] [IsMemOne S α] (f: F) (s: S) : MemOne (Set.image f s) := by
  show 1 ∈ _; simp
  exists 1; exact ⟨mem_one s, map_one _⟩

public theorem copy [One α] [SetLike S α] [IsMemOne S α]
  (u: Set α) (h: ∃s: S, u = s) : MemOne u:= by
  obtain ⟨s, rfl⟩ := h
  exact mem_one s

public theorem copy' [One α] [SetLike S α] [IsMemOne S α]
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemOne u:= by
  apply (h _).mp
  apply mem_one

end MemOne

namespace MemZero

public theorem preimage
  [Zero α] [Zero β] [Funlike F α β] [IsZeroHom F α β]
  [SetLike S β] [IsMemZero S β] (f: F) (s: S) : MemZero (Set.preimage f s) := by
  show f 0 ∈ s
  rw [map_zero]
  apply mem_zero

public theorem image
  [Zero α] [Zero β] [Funlike F α β] [IsZeroHom F α β]
  [SetLike S α] [IsMemZero S α] (f: F) (s: S) : MemZero (Set.image f s) := by
  show 0 ∈ _; simp
  exists 0; exact ⟨mem_zero s, map_zero _⟩

public theorem copy [Zero α] [SetLike S α] [IsMemZero S α]
  (u: Set α) (h: ∃s: S, u = s) : MemZero u:= by
  obtain ⟨s, rfl⟩ := h
  exact mem_zero s

public theorem copy' [Zero α] [SetLike S α] [IsMemZero S α]
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemZero u:= by
  apply (h _).mp
  apply mem_zero

end MemZero

namespace Submonoid

variable [One α] [Mul α]

inductive Closure [Mul α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| one : Closure U 1
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a * b)

public def closure (U: Set α) : Submonoid α where
  toSet := { Mem := Closure U }
  mem_one := Closure.one
  mem_mul := Closure.mul

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemOne S α] [IsMemMul S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | one => apply mem_one
  | mul => apply mem_mul <;> assumption

public instance : Top (Submonoid α) where
   top := {
    toSet := ⊤
    mem_one := True.intro
    mem_mul _ _ := True.intro
   }

public instance [IsLawfulOne α] : Bot (Submonoid α) where
   bot := {
    toSet := {1}
    mem_one := rfl
    mem_mul {a b} := by
      intro rfl rfl; rw [mul_one]; rfl
   }

public theorem bot_sub [IsLawfulOne α] (a: Submonoid α) : ⊥ ⊆ a := by intro x rfl; exact mem_one a
public theorem sub_top (a: Submonoid α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemOne S α] [IsMemMul S α]

@[expose] public def of (s: S) : Submonoid α where
  toSet := s
  mem_one := mem_one s
  mem_mul := mem_mul s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : Submonoid α where
  toSet := u
  mem_one := MemOne.copy' hu
  mem_mul := MemMul.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

variable [One β] [Mul β] [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]

@[expose] public def preimage (f: F) (s: Submonoid β) : Submonoid α where
  toSet := Set.preimage f s
  mem_one := MemOne.preimage f s
  mem_mul := MemMul.preimage f s
@[expose] public def image (f: F) (s: Submonoid α) : Submonoid β where
  toSet := Set.image f s
  mem_one := MemOne.image f s
  mem_mul := MemMul.image f s

@[simp] public theorem mem_preimage {f: F} {s: Submonoid β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Submonoid α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end Submonoid

namespace AddSubmonoid

variable [Zero α] [Add α]

inductive Closure [Add α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| zero : Closure U 0
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)

public def closure (U: Set α) : AddSubmonoid α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_add := Closure.add

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemZero S α] [IsMemAdd S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | add => apply mem_add <;> assumption

public instance : Top (AddSubmonoid α) where
   top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ := True.intro
   }

public instance [IsLawfulZero α] : Bot (AddSubmonoid α) where
   bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add {a b} := by
      intro rfl rfl; rw [add_zero]; rfl
   }

public theorem bot_sub [IsLawfulZero α] (a: AddSubmonoid α) : ⊥ ⊆ a := by intro x rfl; exact mem_zero a
public theorem sub_top (a: AddSubmonoid α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemZero S α] [IsMemAdd S α]

@[expose] public def of (s: S) : AddSubmonoid α where
  toSet := s
  mem_zero := mem_zero s
  mem_add := mem_add s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : AddSubmonoid α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_add := MemAdd.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

variable [Zero β] [Add β] [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]

@[expose] public def preimage (f: F) (s: AddSubmonoid β) : AddSubmonoid α where
  toSet := Set.preimage f s
  mem_zero := MemZero.preimage f s
  mem_add := MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubmonoid α) : AddSubmonoid β where
  toSet := Set.image f s
  mem_zero := MemZero.image f s
  mem_add := MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubmonoid β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubmonoid α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end AddSubmonoid

variable [SetLike S α]

public instance [Zero α] [IsMemZero S α] : IsMemOne (MulOfAdd S) (MulOfAdd α) where
  mem_one := mem_zero (S := S) (α := α)
public instance [One α] [IsMemOne S α] : IsMemZero (AddOfMul S) (AddOfMul α) where
  mem_zero := mem_one (S := S) (α := α)

public theorem mem_pown
  [MonoidOps α] [IsMonoid α]
  [IsMemOne S α] [IsMemMul S α]
  (a: α) (n: ℕ) (s: S) : a ∈ s -> a ^ n ∈ s := by
  intro h
  induction n with
  | zero => rw [pown_zero]; apply mem_one
  | succ n ih =>
    rw [pown_succ]; apply mem_mul
    assumption
    assumption

public theorem mem_nsmul
  [AddMonoidOps α] [IsAddMonoid α]
  [IsMemZero S α] [IsMemAdd S α]
  (a: α) (n: ℕ) (s: S) : a ∈ s -> n • a ∈ s :=
  mem_pown (S := MulOfAdd S) (α := MulOfAdd α) _ _ _

public instance [One α] [IsMemOne S α] (s: S) : One s where
  one := {
    val := 1
    property := mem_one s
  }

public instance [Zero α] [IsMemZero S α] (s: S) : Zero s where
  zero := {
    val := 0
    property := mem_zero s
  }

public instance [MonoidOps α] [IsMonoid α] [IsMemOne S α] [IsMemMul S α] (s: S) : Pow s ℕ where
  pow a n := {
    val := a.val ^ n
    property := mem_pown _ n s a.property
  }

public instance [AddMonoidOps α] [IsAddMonoid α] [IsMemZero S α] [IsMemAdd S α] (s: S) : SMul ℕ s where
  smul n a := {
    val := n • a.val
    property := mem_nsmul _ n s a.property
  }

@[simp] public theorem subtype_one [One α] [IsMemOne S α] {s: S} : (1: (s: Type _)).val = 1 := rfl
@[simp] public theorem subtype_zero [Zero α] [IsMemZero S α] {s: S} : (0: (s: Type _)).val = 0 := rfl
@[simp] public theorem subtype_pown [MonoidOps α] [IsMonoid α] [IsMemOne S α] [IsMemMul S α] {s: S} (a: (s: Type _)) (n: ℕ) : (a ^ n).val = a.val ^ n := rfl
@[simp] public theorem subtype_nsmul [AddMonoidOps α] [IsAddMonoid α] [IsMemZero S α] [IsMemAdd S α] {s: S} (a: (s: Type _)) (n: ℕ) : (n • a).val = n • a.val := rfl

public instance [Mul α] [Zero α] [IsMemMul S α] [IsMemZero S α] [IsLeftCancel₀ α] (s: S) : IsLeftCancel₀ s where
  of_mul_left₀ {k a b} hk h := by
    ext; apply of_mul_left₀ (k := k.val)
    intro g; apply hk; ext; assumption
    exact congrArg Subtype.val h
public instance [Mul α] [Zero α] [IsMemMul S α] [IsMemZero S α] [IsRightCancel₀ α] (s: S) : IsRightCancel₀ s where
  of_mul_right₀ {k a b} hk h := by
    ext; apply of_mul_right₀ (k := k.val)
    intro g; apply hk; ext; assumption
    exact congrArg Subtype.val h

public instance [One α] [Mul α] [IsMemOne S α] [IsMemMul S α] [IsLawfulOne α] (s: S) : IsLawfulOne s where
  one_mul a := by ext; apply one_mul
  mul_one a := by ext; apply mul_one
public instance [Zero α] [Mul α] [IsMemZero S α] [IsMemMul S α] [IsLawfulZeroMul α] (s: S) : IsLawfulZeroMul s where
  zero_mul a := by ext; apply zero_mul
  mul_zero a := by ext; apply mul_zero
public instance [Zero α] [Add α] [IsMemZero S α] [IsMemAdd S α] [IsLawfulZero α] (s: S) : IsLawfulZero s where
  zero_add a := by ext; apply zero_add
  add_zero a := by ext; apply add_zero

public instance [MonoidOps α] [IsMemOne S α] [IsMemMul S α] [IsMonoid α] (s: S) : IsMonoid s where
  pown_zero a := by ext; apply pown_zero
  pown_succ a n := by ext; apply pown_succ

public instance [AddMonoidOps α] [IsMemZero S α] [IsMemAdd S α] [IsAddMonoid α] (s: S) : IsAddMonoid s where
  zero_nsmul a := by ext; apply zero_nsmul
  succ_nsmul a n := by ext; apply succ_nsmul
