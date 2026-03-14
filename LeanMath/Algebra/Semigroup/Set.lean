import LeanMath.Algebra.Semigroup.Defs
import LeanMath.Data.Set.Defs

attribute [local irreducible] AddOfMul MulOfAdd

instance [SetLike S α] : SetLike (AddOfMul S) (AddOfMul α) where
  coeSet a := (Set.coe a.get).preimage AddOfMul.get
  coeInj := by
    intro a b h
    dsimp at h
    show AddOfMul.mk (AddOfMul.get a) = AddOfMul.mk (AddOfMul.get b)
    congr 1
    apply Set.coe_inj
    ext x
    apply Iff.intro
    intro hx
    replace hx : AddOfMul.get (AddOfMul.mk x) ∈ _ := hx
    rwa [←Set.mem_preimage, h, Set.mem_preimage] at hx
    intro hx
    replace hx : AddOfMul.get (AddOfMul.mk x) ∈ _ := hx
    rwa [←Set.mem_preimage, ←h, Set.mem_preimage] at hx

instance [SetLike S α] : SetLike (MulOfAdd S) (MulOfAdd α) where
  coeSet a := (Set.coe a.get).preimage MulOfAdd.get
  coeInj := by
    intro a b h
    dsimp at h
    show MulOfAdd.mk (MulOfAdd.get a) = MulOfAdd.mk (MulOfAdd.get b)
    congr 1
    apply Set.coe_inj
    ext x
    apply Iff.intro
    intro hx
    replace hx : MulOfAdd.get (MulOfAdd.mk x) ∈ _ := hx
    rwa [←Set.mem_preimage, h, Set.mem_preimage] at hx
    intro hx
    replace hx : MulOfAdd.get (MulOfAdd.mk x) ∈ _ := hx
    rwa [←Set.mem_preimage, ←h, Set.mem_preimage] at hx

def MemMul [SetLike S α] [Mul α] (s: S) := ∀⦃a b: α⦄, a ∈ s -> b ∈ s -> a * b ∈ s
def MemAdd [SetLike S α] [Add α] (s: S) := ∀⦃a b: α⦄, a ∈ s -> b ∈ s -> a + b ∈ s

class IsMemMul (S α: Type*) [Mul α] [SetLike S α] where
  protected mem_mul (s: S) : MemMul s := by intro s; exact s.mem_mul

class IsMemAdd (S α: Type*) [Add α] [SetLike S α] where
  protected mem_add (s: S) : MemAdd s := by intro s; exact s.mem_add

def mem_mul [Mul α] [SetLike S α] [IsMemMul S α] (s: S) : MemMul s :=
  IsMemMul.mem_mul _

def mem_add [Add α] [SetLike S α] [IsMemAdd S α] (s: S) : MemAdd s :=
  IsMemAdd.mem_add _

structure SubSemigroup (α: Type*) [Mul α] where
  toSet: Set α
  protected mem_mul : MemMul toSet

structure AddSubSemigroup (α: Type*) [Add α] where
  toSet: Set α
  protected mem_add : MemAdd toSet

instance [Mul α] : SetLike (SubSemigroup α) α where
instance [Mul α] : IsMemMul (SubSemigroup α) α where

instance [Add α] : SetLike (AddSubSemigroup α) α where
instance [Add α] : IsMemAdd (AddSubSemigroup α) α where

section

variable [Mul α] [Mul β]

def MemMul.preimage [SetLike S β] [IsMemMul S β] [FunLike F α β] [IsMulHom F α β]
  (f: F) (U: S) : MemMul (Set.preimage f U) := by
    intro a b ha hb
    show f (a * b) ∈ U
    rw [map_mul]
    apply mem_mul
    assumption
    assumption

def MemMul.image [SetLike S α] [IsMemMul S α] [FunLike F α β] [IsMulHom F α β]
  (f: F) (U: S) : MemMul (Set.image f U) := by
    rintro a b ⟨a, _, rfl⟩ ⟨b, _, rfl⟩
    rw [←map_mul]
    apply Set.mem_image'
    apply mem_mul U
    assumption
    assumption

namespace SubSemigroup

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| mul ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a * b)

def closure (U: Set α) : SubSemigroup α where
  toSet := Set.ofMem (Closure U)
  mem_mul := Closure.mul

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a ha
  apply Closure.of
  assumption

def of_mem_closure [SetLike S α] [IsMemMul S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | mul a b iha ihb =>
    apply mem_mul
    assumption
    assumption

instance : Top (SubSemigroup α) where
  top := {
    toSet := ⊤
    mem_mul _ _ _ _ := True.intro
  }

instance : Bot (SubSemigroup α) where
  bot := {
    toSet := ⊥
    mem_mul := nofun
  }

def mem_top (a: α) : a ∈ (⊤: SubSemigroup α) := True.intro
def not_mem_bot (a: α) : a ∉ (⊥: SubSemigroup α) := nofun
def sub_top (a: SubSemigroup α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub (a: SubSemigroup α) : ⊥ ⊆ a := nofun

def preimage (f: α →*ₙ β) (U: SubSemigroup β) : SubSemigroup α where
  toSet := Set.preimage f U
  mem_mul := MemMul.preimage f _

def image (f: α →*ₙ β) (U: SubSemigroup α) : SubSemigroup β where
  toSet := Set.image f U
  mem_mul := MemMul.image f _

end SubSemigroup

end

section

variable [Add α] [Add β]

def MemAdd.preimage [SetLike S β] [IsMemAdd S β] [FunLike F α β] [IsAddHom F α β]
  (f: F) (U: S) : MemAdd (Set.preimage f U) := by
    intro a b ha hb
    show f (a + b) ∈ U
    rw [map_add]
    apply mem_add
    assumption
    assumption

def MemAdd.image [SetLike S α] [IsMemAdd S α] [FunLike F α β] [IsAddHom F α β]
  (f: F) (U: S) : MemAdd (Set.image f U) := by
    rintro a b ⟨a, _, rfl⟩ ⟨b, _, rfl⟩
    rw [←map_add]
    apply Set.mem_image'
    apply mem_add U
    assumption
    assumption

namespace AddSubSemigroup

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| add ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a + b)

def closure (U: Set α) : AddSubSemigroup α where
  toSet := Set.ofMem (Closure U)
  mem_add := Closure.add

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a ha
  apply Closure.of
  assumption

def of_mem_closure [SetLike S α] [IsMemAdd S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | add a b iha ihb =>
    apply mem_add
    assumption
    assumption

instance : Top (AddSubSemigroup α) where
  top := {
    toSet := ⊤
    mem_add _ _ _ _ := True.intro
  }

instance : Bot (AddSubSemigroup α) where
  bot := {
    toSet := ⊥
    mem_add := nofun
  }

def mem_top (a: α) : a ∈ (⊤: AddSubSemigroup α) := True.intro
def not_mem_bot (a: α) : a ∉ (⊥: AddSubSemigroup α) := nofun
def sub_top (a: AddSubSemigroup α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub (a: AddSubSemigroup α) : ⊥ ⊆ a := nofun

def preimage (f: α →+ₙ β) (U: AddSubSemigroup β) : AddSubSemigroup α where
  toSet := Set.preimage f U
  mem_add := MemAdd.preimage f _

def image (f: α →+ₙ β) (U: AddSubSemigroup α) : AddSubSemigroup β where
  toSet := Set.image f U
  mem_add := MemAdd.image f _

end AddSubSemigroup

end

variable (s: S)
variable [Mul α] [SetLike S α] [IsMemMul S α]

instance : IsMemAdd (AddOfMul S) (AddOfMul α) where
  mem_add := by
    intro s a b ha hb
    apply mem_mul s.get
    assumption
    assumption

instance : Mul s where
  mul a b := {
    val := a.val * b.val
    property := mem_mul s a.property b.property
  }

instance [IsSemigroup α] : IsSemigroup s where
  mul_assoc a b c := by
    apply Subtype.val_inj
    apply mul_assoc

instance [IsComm α] : IsComm s where
  mul_comm a b := by
    apply Subtype.val_inj
    apply mul_comm

variable [Add α] [SetLike S α] [IsMemAdd S α]

instance : IsMemMul (MulOfAdd S) (MulOfAdd α) where
  mem_mul := by
    intro s a b ha hb
    apply mem_add s.get
    assumption
    assumption

instance : Add s where
  add a b := {
    val := a.val + b.val
    property := mem_add s a.property b.property
  }

instance [IsAddSemigroup α] : IsAddSemigroup s where
  add_assoc a b c := by
    apply Subtype.val_inj
    apply add_assoc

instance [IsAddComm α] : IsAddComm s where
  add_comm a b := by
    apply Subtype.val_inj
    apply add_comm
