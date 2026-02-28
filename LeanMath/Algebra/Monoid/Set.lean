import LeanMath.Algebra.Monoid.Defs
import LeanMath.Algebra.Semigroup.Set

class IsMemOne (S α: Type*) [One α] [SetLike S α] where
  protected mem_one (s: S): 1 ∈ s := by intro s; exact s.mem_one

class IsMemZero (S α: Type*) [Zero α] [SetLike S α] where
  protected mem_zero (s: S): 0 ∈ s := by intro s; exact s.mem_zero

def mem_one [One α] [SetLike S α] [IsMemOne S α] (s: S) : 1 ∈ s :=
  IsMemOne.mem_one _

def mem_zero [Zero α] [SetLike S α] [IsMemZero S α] (s: S) : 0 ∈ s :=
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
