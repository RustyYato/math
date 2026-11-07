module

public import Math.Algebra.Monoid.Defs

namespace Math

variable {ι: Type*} {α: ι -> Type*}

public class GradedOne [Zero ι] (α: ι -> Type*) where
  gOne : α 0

public class GradedMul [Add ι] (α: ι -> Type*) where
  gMul {i j: ι} (a: α i) (b: α j) : α (i + j)

public class GradedPow (α: ι -> Type*) (R: Type*) [SMul R ι] where
  gPow {i: ι} (a: α i) (n: R) : α (n • i)

public instance [Zero ι] [GradedOne α] : One (α 0) where
  one := GradedOne.gOne
public instance [Add ι] [GradedMul α] : HMul (α i) (α j) (α (i + j)) where
  hMul := GradedMul.gMul

public class IsLawfulGradedOne [Add ι] [Zero ι] [IsLawfulZero ι] (α: ι -> Type*) [GradedOne α] [GradedMul α] where
  gone_gmul (a: α i) : (1: α 0) * a ≍ a
  gmul_gone (a: α i) : a * (1: α 0) ≍ a

public class IsLawfulGradedPowN [AddMonoidOps ι] [IsLawfulNSMul ι] (α: ι -> Type*) [GradedOne α] [GradedMul α] [GradedPow α ℕ] where
  gpown_zero (a: α i) : GradedPow.gPow a 0 ≍ (1: α 0)
  gpown_succ (a: α i) (n: ℕ) : GradedPow.gPow a (n + 1) ≍ GradedPow.gPow a n * a

public class IsGradedSemigroup [Add ι] [IsAddSemigroup ι] (α: ι -> Type*) [GradedMul α] where
  gmul_assoc (a: α i) (b: α j) (c: α k) : a * b * c ≍ a * (b * c)

public class GradedMonoidOps [AddMonoidOps ι] (α: ι -> Type*) extends GradedOne α, GradedMul α, GradedPow α ℕ where

public instance [AddMonoidOps ι] [GradedOne α] [GradedMul α] [GradedPow α ℕ] : GradedMonoidOps α where

public class IsGradedMonoid [AddMonoidOps ι] [IsAddMonoid ι] (α: ι -> Type*) [GradedOne α] [GradedMul α] [GradedPow α ℕ]
  extends IsLawfulGradedOne α, IsLawfulGradedPowN α, IsGradedSemigroup α where

@[ext]
public structure GradedMonoid (α: ι -> Type*) where
  grade: ι
  value: α grade

public instance [Zero ι] [GradedOne α] : One (GradedMonoid α) where
  one := {
    grade := 0
    value := 1
  }

public instance [Add ι] [GradedMul α] : Mul (GradedMonoid α) where
  mul a b := {
    grade := a.grade + b.grade
    value := a.value * b.value
  }

public instance [SMul R ι] [GradedPow α R] : Pow (GradedMonoid α) R where
  pow a r := {
    grade := r • a.grade
    value :=GradedPow.gPow a.value r
  }

public instance
  [Zero ι] [Add ι] [IsLawfulZero ι]
  [GradedOne α] [GradedMul α] [IsLawfulGradedOne α]
  : IsLawfulOne (GradedMonoid α) where
  mul_one a := by ext; apply add_zero; apply IsLawfulGradedOne.gmul_gone
  one_mul a := by ext; apply zero_add; apply IsLawfulGradedOne.gone_gmul

public instance
  [Zero ι] [Add ι] [SMul ℕ ι] [IsLawfulNSMul ι]
  [GradedOne α] [GradedMul α] [GradedPow α ℕ] [IsLawfulGradedPowN α]
  : IsLawfulPowN (GradedMonoid α) where
  pown_zero a := by ext; apply zero_nsmul; apply IsLawfulGradedPowN.gpown_zero
  pown_succ a b := by ext; apply succ_nsmul; apply IsLawfulGradedPowN.gpown_succ

public instance
  [Add ι] [IsAddSemigroup ι]
  [GradedMul α] [IsGradedSemigroup α]
  : IsSemigroup (GradedMonoid α) where
  mul_assoc a b c := by ext; apply add_assoc; apply IsGradedSemigroup.gmul_assoc

public instance
  [AddMonoidOps ι] [IsAddMonoid ι]
  [GradedMonoidOps α] [IsGradedMonoid α]
  : IsMonoid (GradedMonoid α) where

variable {α: Type*}

instance [Zero ι] [One α] : GradedOne (fun _: ι => α) where
  gOne := 1

instance [Add ι] [Mul α] : GradedMul (fun _: ι => α) where
  gMul a b := a * b

instance [SMul R ι] [Pow α R] : GradedPow (fun _: ι => α) R where
  gPow a r := a ^ r

instance [Zero ι] [Add ι] [IsLawfulZero ι] [One α] [Mul α] [IsLawfulOne α] : IsLawfulGradedOne (fun _: ι => α) where
  gone_gmul a := heq_of_eq (one_mul a)
  gmul_gone a := heq_of_eq (mul_one a)

instance [Zero ι] [Add ι] [SMul ℕ ι] [IsLawfulNSMul ι] [One α] [Mul α] [Pow α ℕ] [IsLawfulPowN α] : IsLawfulGradedPowN (fun _: ι => α) where
  gpown_zero a := heq_of_eq (pown_zero a)
  gpown_succ a n := heq_of_eq (pown_succ a n)

instance [Add ι] [IsAddSemigroup ι] [Mul α] [IsSemigroup α] : IsGradedSemigroup (fun _: ι => α) where
  gmul_assoc a b c := heq_of_eq (mul_assoc a b c)

instance [AddMonoidOps ι] [IsAddMonoid ι] [MonoidOps α] [IsMonoid α] : IsGradedMonoid (fun _: ι => α) where
