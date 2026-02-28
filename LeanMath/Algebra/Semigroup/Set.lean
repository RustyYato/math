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

class IsMemMul (S α: Type*) [Mul α] [SetLike S α] where
  protected mem_mul (s: S) {a b: α} : a ∈ s -> b ∈ s -> a * b ∈ s := by intro s; exact s.mem_mul

class IsMemAdd (S α: Type*) [Add α] [SetLike S α] where
  protected mem_add (s: S) {a b: α} : a ∈ s -> b ∈ s -> a + b ∈ s := by intro s; exact s.mem_add

def mem_mul [Mul α] [SetLike S α] [IsMemMul S α] (s: S) {a b: α} : a ∈ s -> b ∈ s -> a * b ∈ s :=
  IsMemMul.mem_mul _

def mem_add [Add α] [SetLike S α] [IsMemAdd S α] (s: S) {a b: α} : a ∈ s -> b ∈ s -> a + b ∈ s :=
  IsMemAdd.mem_add _

structure SubSemigroup (α: Type*) [Mul α] where
  toSet: Set α
  protected mem_mul {a b: α} : a ∈ toSet -> b ∈ toSet -> a * b ∈ toSet

structure AddSubSemigroup (α: Type*) [Add α] where
  toSet: Set α
  protected mem_add {a b: α} : a ∈ toSet -> b ∈ toSet -> a + b ∈ toSet

instance [Mul α] : SetLike (SubSemigroup α) α where
instance [Mul α] : IsMemMul (SubSemigroup α) α where

instance [Add α] : SetLike (AddSubSemigroup α) α where
instance [Add α] : IsMemAdd (AddSubSemigroup α) α where

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
