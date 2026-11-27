module

public import Math.Algebra.Semigroup.Defs.Prod
public import Math.Algebra.Monoid.Defs.Basic

namespace Math

variable {ι α β: Type*} {γ: ι -> Type*}

section Mul

public instance [One α] [One β] : One (α × β) where
  one := (1, 1)

public instance [Pow α X] [Pow β X] : Pow (α × β) X where
  pow a x := (a.fst ^ x, a.snd ^ x)

public instance [One α] [One β] [Mul α] [Mul β] [IsLawfulOne α] [IsLawfulOne β] : IsLawfulOne (α × β) where
  mul_one a := by ext <;> apply mul_one
  one_mul a := by ext <;> apply one_mul

public instance [One α] [One β] [Mul α] [Mul β] [Pow α ℕ] [Pow β ℕ] [IsLawfulPowN α] [IsLawfulPowN β] : IsLawfulPowN (α × β) where
  pown_zero a := by ext <;> apply pown_zero
  pown_succ a _ := by ext <;> apply pown_succ

public instance [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β] : IsMonoid (α × β) where

public instance [∀i, One (γ i)] : One (∀i, γ i) where
  one _ := 1

public instance [∀i, Pow (γ i) X] : Pow (∀i, γ i) X where
  pow a x _ := a _ ^ x

public instance [∀i, One (γ i)] [∀i, Mul (γ i)] [∀i, IsLawfulOne (γ i)] : IsLawfulOne (∀i, γ i) where
  mul_one a := by ext <;> apply mul_one
  one_mul a := by ext <;> apply one_mul

public instance [∀i, One (γ i)] [∀i, Mul (γ i)] [∀i, Pow (γ i) ℕ] [∀i, IsLawfulPowN (γ i)] : IsLawfulPowN (∀i, γ i) where
  pown_zero a := by ext <;> apply pown_zero
  pown_succ a _ := by ext <;> apply pown_succ

public instance [∀i, MonoidOps (γ i)] [∀i, IsMonoid (γ i)] : IsMonoid (∀i, γ i) where

public instance [One α] : One (ι -> α) := inferInstance
public instance [Pow α X] : Pow (ι -> α) X := inferInstance
public instance [One α] [Mul α] [IsLawfulOne α] : IsLawfulOne (ι -> α) := inferInstance
public instance [One α] [Mul α] [Pow α ℕ] [IsLawfulPowN α] : IsLawfulPowN (ι -> α) := inferInstance
public instance [MonoidOps α] [IsMonoid α] : IsMonoid (ι -> α) := inferInstance

end Mul

section Add

public instance [Zero α] [Zero β] : Zero (α × β) where
  zero := (0, 0)

public instance [SMul X α] [SMul X β] : SMul X (α × β) where
  smul x a := (x • a.fst, x • a.snd)

public instance [Zero α] [Zero β] [Add α] [Add β] [IsLawfulZero α] [IsLawfulZero β] : IsLawfulZero (α × β) where
  add_zero a := by ext <;> apply add_zero
  zero_add a := by ext <;> apply zero_add

public instance [Zero α] [Zero β] [Mul α] [Mul β] [IsLawfulZeroMul α] [IsLawfulZeroMul β] : IsLawfulZeroMul (α × β) where
  mul_zero a := by ext <;> apply mul_zero
  zero_mul a := by ext <;> apply zero_mul

public instance [Zero α] [Zero β] [Add α] [Add β] [SMul ℕ α] [SMul ℕ β] [IsLawfulNSMul α] [IsLawfulNSMul β] : IsLawfulNSMul (α × β) where
  zero_nsmul a := by ext <;> apply zero_nsmul
  succ_nsmul a _ := by ext <;> apply succ_nsmul

public instance [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β] : IsMonoid (α × β) where

public instance [∀i, Zero (γ i)] : Zero (∀i, γ i) where
  zero _ := 0

public instance [∀i, SMul X (γ i)] : SMul X (∀i, γ i) where
  smul x a _ := x • a _

public instance [∀i, Zero (γ i)] [∀i, Add (γ i)] [∀i, IsLawfulZero (γ i)] : IsLawfulZero (∀i, γ i) where
  add_zero a := by ext <;> apply add_zero
  zero_add a := by ext <;> apply zero_add

public instance [∀i, Zero (γ i)] [∀i, Mul (γ i)] [∀i, IsLawfulZeroMul (γ i)] : IsLawfulZeroMul (∀i, γ i) where
  mul_zero a := by ext <;> apply mul_zero
  zero_mul a := by ext <;> apply zero_mul

public instance [∀i, Zero (γ i)] [∀i, Add (γ i)] [∀i, SMul ℕ (γ i)] [∀i, IsLawfulNSMul (γ i)] : IsLawfulNSMul (∀i, γ i) where
  zero_nsmul a := by ext <;> apply zero_nsmul
  succ_nsmul a _ := by ext <;> apply succ_nsmul

public instance [∀i, MonoidOps (γ i)] [∀i, IsMonoid (γ i)] : IsMonoid (∀i, γ i) where

public instance [Zero α] : Zero (ι -> α) := inferInstance
public instance [Pow α X] : Pow (ι -> α) X := inferInstance
public instance [Zero α] [Add α] [IsLawfulZero α] : IsLawfulZero (ι -> α) := inferInstance
public instance [Zero α] [Mul α] [IsLawfulZeroMul α] : IsLawfulZeroMul (ι -> α) := inferInstance
public instance [Zero α] [Add α] [SMul ℕ α] [IsLawfulNSMul α] : IsLawfulNSMul (ι -> α) := inferInstance
public instance [MonoidOps α] [IsMonoid α] : IsMonoid (ι -> α) := inferInstance

end Add
