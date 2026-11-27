module

public import Math.Algebra.AddMonoidWithOne.Defs.Prod
public import Math.Algebra.Semiring.Defs.Basic

namespace Math

variable {ι α β: Type*} {γ: ι -> Type*}

public instance [Add α] [Add β] [Mul α] [Mul β] [IsLeftDistrib α] [IsLeftDistrib β] : IsLeftDistrib (α × β) where
  mul_add _ _ _  := by ext <;> apply mul_add
public instance [Add α] [Add β] [Mul α] [Mul β] [IsRightDistrib α] [IsRightDistrib β] : IsRightDistrib (α × β) where
  add_mul _ _ _  := by ext <;> apply add_mul

public instance [AddMonoidOps α] [Mul α] [AddMonoidOps β] [Mul β]
  [IsNonUnitalNonAssocSemiring α] [IsNonUnitalNonAssocSemiring β]
  : IsNonUnitalNonAssocSemiring (α × β) where

public instance [AddMonoidOps α] [Mul α] [AddMonoidOps β] [Mul β]
  [IsNonUnitalSemiring α] [IsNonUnitalSemiring β]
  : IsNonUnitalSemiring (α × β) where

public instance [AddMonoidOps α] [Mul α] [One α] [NatCast α]
  [AddMonoidOps β] [Mul β] [One β] [NatCast β]
  [IsNonAssocSemiring α] [IsNonAssocSemiring β]
  : IsNonAssocSemiring (α × β) where

public instance [SemiringOps α] [SemiringOps β] [IsSemiring α] [IsSemiring β] : IsSemiring (α × β) where

public instance [∀i, Add (γ i)] [∀i, Mul (γ i)] [∀i, IsLeftDistrib (γ i)] : IsLeftDistrib (∀i, γ i) where
  mul_add _ _ _  := by ext <;> apply mul_add
public instance [∀i, Add (γ i)] [∀i, Mul (γ i)] [∀i, IsRightDistrib (γ i)] : IsRightDistrib (∀i, γ i) where
  add_mul _ _ _  := by ext <;> apply add_mul

public instance [∀i, AddMonoidOps (γ i)] [∀i, Mul (γ i)]
  [∀i, IsNonUnitalNonAssocSemiring (γ i)]
  : IsNonUnitalNonAssocSemiring (∀i, γ i) where

public instance [∀i, AddMonoidOps (γ i)] [∀i, Mul (γ i)]
  [∀i, IsNonUnitalSemiring (γ i)]
  : IsNonUnitalSemiring (∀i, γ i) where

public instance [∀i, AddMonoidOps (γ i)] [∀i, Mul (γ i)] [∀i, One (γ i)] [∀i, NatCast (γ i)]
  [∀i, IsNonAssocSemiring (γ i)]
  : IsNonAssocSemiring (∀i, γ i) where

public instance [∀i, SemiringOps (γ i)] [∀i, IsSemiring (γ i)] : IsSemiring (∀i, γ i) where

public instance [Add α] [Mul α] [IsLeftDistrib α] : IsLeftDistrib (ι -> α)
   := inferInstance
public instance [Add α] [Mul α] [IsRightDistrib α] : IsRightDistrib (ι -> α)
   := inferInstance

public instance [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α]
  : IsNonUnitalNonAssocSemiring (ι -> α) := inferInstance

public instance [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α]
  : IsNonUnitalSemiring (ι -> α) := inferInstance

public instance [AddMonoidOps α] [Mul α] [One α] [NatCast α] [IsNonAssocSemiring α]
  : IsNonAssocSemiring (ι -> α) := inferInstance

public instance [SemiringOps α] [IsSemiring α] : IsSemiring (ι -> α) := inferInstance
