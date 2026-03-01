import LeanMath.Algebra.Monoid.Defs
import LeanMath.Algebra.Semigroup.Set

def MemOne [SetLike S α] [One α] (s: S) := 1 ∈ s
def MemZero [SetLike S α] [Zero α] (s: S) := 0 ∈ s

class IsMemOne (S α: Type*) [One α] [SetLike S α] where
  protected mem_one (s: S): MemOne s := by intro s; exact s.mem_one

class IsMemZero (S α: Type*) [Zero α] [SetLike S α] where
  protected mem_zero (s: S): MemZero s := by intro s; exact s.mem_zero

def mem_one [One α] [SetLike S α] [IsMemOne S α] (s: S) : MemOne s :=
  IsMemOne.mem_one _

def mem_zero [Zero α] [SetLike S α] [IsMemZero S α] (s: S) : MemZero s :=
  IsMemZero.mem_zero _

structure SubOne (α: Type*) [One α] where
  toSet: Set α
  protected mem_one : 1 ∈ toSet

structure SubZero (α: Type*) [Zero α] where
  toSet: Set α
  protected mem_zero : 0 ∈ toSet

instance [One α] : SetLike (SubOne α) α where
instance [One α] : IsMemOne (SubOne α) α where

instance [Zero α] : SetLike (SubZero α) α where
instance [Zero α] : IsMemZero (SubZero α) α where

structure SubMonoid (α: Type*) [One α] [Mul α] extends SubOne α, SubSemigroup α where
structure AddSubMonoid (α: Type*) [Zero α] [Add α] extends SubZero α, AddSubSemigroup α where

instance [One α] [Mul α] : SetLike (SubMonoid α) α where
instance [One α] [Mul α] : IsMemOne (SubMonoid α) α where
instance [One α] [Mul α] : IsMemMul (SubMonoid α) α where

instance [Zero α] [Add α] : SetLike (AddSubMonoid α) α where
instance [Zero α] [Add α] : IsMemZero (AddSubMonoid α) α where
instance [Zero α] [Add α] : IsMemAdd (AddSubMonoid α) α where

section

variable [Mul α] [Mul β] [One α] [One β]

def MemOne.preimage [SetLike S β] [IsMemOne S β] [FunLike F α β] [IsOneHom F α β]
  (f: F) (U: S) : MemOne (Set.preimage f U) := by
    show f 1 ∈ U
    rw [map_one]
    apply mem_one

def MemOne.image [SetLike S α] [IsMemOne S α] [FunLike F α β] [IsOneHom F α β]
  (f: F) (U: S) : MemOne (Set.image f U) := by
    show 1 ∈ _
    rw [←map_one f]
    apply Set.mem_image'
    apply mem_one U

namespace SubMonoid

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| one : Closure U 1
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a * b)

def closure (U: Set α) : SubMonoid α where
  toSet := Set.ofMem (Closure U)
  mem_one := Closure.one
  mem_mul := Closure.mul

def sub_closure (U: Set α) : U ⊆ SubSemigroup.closure U := by
  intro a ha
  apply SubSemigroup.Closure.of
  assumption

def of_mem_closure [SetLike S α] [IsMemMul S α] [IsMemOne S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | one => apply mem_one
  | mul a b iha ihb =>
    apply mem_mul <;> assumption

instance : Top (SubMonoid α) where
  top := {
    toSet := ⊤
    mem_one := True.intro
    mem_mul _ _ := True.intro
  }

instance [IsLawfulOneMul α] : Bot (SubMonoid α) where
  bot := {
    toSet := {1}
    mem_one := rfl
    mem_mul := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
  }

def mem_top (a: α) : a ∈ (⊤: SubMonoid α) := True.intro
def sub_top (a: SubMonoid α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub [IsLawfulOneMul α] (a: SubMonoid α) : ⊥ ⊆ a := by
  rintro _ rfl
  apply mem_one a
@[simp] def closure_bot_eq_bot [IsLawfulOneMul α] : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

def preimage (f: α →* β) (U: SubMonoid β) : SubMonoid α where
  toSet := Set.preimage f U
  mem_one := MemOne.preimage f _
  mem_mul := MemMul.preimage f _

def image (f: α →* β) (U: SubMonoid α) : SubMonoid β where
  toSet := Set.image f U
  mem_one := MemOne.image f _
  mem_mul := MemMul.image f _

def kernel [IsLawfulOneMul β] (f: α →* β) : SubMonoid α := preimage f ⊥

end SubMonoid

end

section

variable [Add α] [Add β] [Zero α] [Zero β]

def MemZero.preimage [SetLike S β] [IsMemZero S β] [FunLike F α β] [IsZeroHom F α β]
  (f: F) (U: S) : MemZero (Set.preimage f U) := by
    show f 0 ∈ U
    rw [map_zero]
    apply mem_zero

def MemZero.image [SetLike S α] [IsMemZero S α] [FunLike F α β] [IsZeroHom F α β]
  (f: F) (U: S) : MemZero (Set.image f U) := by
    show 0 ∈ _
    rw [←map_zero f]
    apply Set.mem_image'
    apply mem_zero U

namespace AddSubMonoid

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)

def closure (U: Set α) : AddSubMonoid α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_add := Closure.add

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a ha
  apply Closure.of
  assumption

def of_mem_closure [SetLike S α] [IsMemAdd S α] [IsMemZero S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | add a b iha ihb =>
    apply mem_add <;> assumption

instance : Top (AddSubMonoid α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ := True.intro
  }

instance [IsLawfulZeroAdd α] : Bot (AddSubMonoid α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]
      rfl
  }

def mem_top (a: α) : a ∈ (⊤: AddSubMonoid α) := True.intro
def sub_top (a: AddSubMonoid α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub [IsLawfulZeroAdd α] (a: AddSubMonoid α) : ⊥ ⊆ a := by
  rintro _ rfl
  apply mem_zero a
@[simp] def closure_bot_eq_bot [IsLawfulZeroAdd α] : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

def preimage (f: α →+ β) (U: AddSubMonoid β) : AddSubMonoid α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_add := MemAdd.preimage f _

def image (f: α →+ β) (U: AddSubMonoid α) : AddSubMonoid β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_add := MemAdd.image f _

def kernel [IsLawfulZeroAdd β] (f: α →+ β) : AddSubMonoid α := preimage f ⊥

end AddSubMonoid

end

variable (s: S) [SetLike S α]

section

instance [One α] [IsMemOne S α] : One s where
  one := {
    val := 1
    property := mem_one s
  }

instance [Zero α] [IsMemZero S α] : Zero s where
  zero := {
    val := 0
    property := mem_zero s
  }

instance [One α] [IsMemOne S α] : IsMemZero (AddOfMul S) (AddOfMul α) where
  mem_zero s := mem_one s.get

instance [Zero α] [IsMemZero S α] : IsMemOne (MulOfAdd S) (MulOfAdd α) where
  mem_one s := mem_zero s.get

instance [One α] [Mul α] [IsMemOne S α] [IsMemMul S α] [IsLawfulOneMul α] : IsLawfulOneMul s where
  one_mul a := by
    apply Subtype.val_inj
    apply one_mul
  mul_one a := by
    apply Subtype.val_inj
    apply mul_one

instance [Zero α] [Mul α] [IsMemZero S α] [IsMemMul S α] [IsLawfulZeroMul α] : IsLawfulZeroMul s where
  zero_mul a := by
    apply Subtype.val_inj
    apply zero_mul
  mul_zero a := by
    apply Subtype.val_inj
    apply mul_zero

instance [Zero α] [Add α] [IsMemZero S α] [IsMemAdd S α] [IsLawfulZeroAdd α] : IsLawfulZeroAdd s where
  zero_add a := by
    apply Subtype.val_inj
    apply zero_add
  add_zero a := by
    apply Subtype.val_inj
    apply add_zero

end

section

variable [MonoidOps α] [IsMonoid α] [IsMemOne S α] [IsMemMul S α]

def mem_npow (s: S) (a: α) (n: ℕ) : a ∈ s -> a ^ n ∈ s := by
  intro h
  induction n with
  | zero =>
    rw [npow_zero]
    apply mem_one
  | succ n ih =>
    rw [npow_succ]
    apply mem_mul
    assumption
    assumption

instance : Pow s ℕ where
  pow a n := {
    val := a.val ^ n
    property := mem_npow s a.val n a.property
  }

instance : IsMonoid s where
  npow_zero _ := by
    apply Subtype.val_inj
    apply npow_zero
  npow_succ _ _ := by
    apply Subtype.val_inj
    apply npow_succ

end

section

variable [AddMonoidOps α] [IsAddMonoid α] [IsMemZero S α] [IsMemAdd S α]

def mem_nsmul (s: S) (n: ℕ) (a: α) : a ∈ s -> n • a ∈ s :=
  mem_npow (MulOfAdd.mk s) (MulOfAdd.mk a) n

instance : SMul ℕ s where
  smul n a := {
    val := n • a.val
    property := mem_nsmul s n a.val a.property
  }

instance : IsAddMonoid s where
  zero_nsmul _ := by
    apply Subtype.val_inj
    apply zero_nsmul
  succ_nsmul _ _ := by
    apply Subtype.val_inj
    apply succ_nsmul

end
