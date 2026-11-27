module

public import Math.Algebra.Semiring.Defs.Prod
public import Math.Algebra.AddGroupWithOne.Defs.Prod
public import Math.Algebra.Ring.Defs.Basic

namespace Math

variable {ι α β: Type*} {γ: ι -> Type*}

public instance [AddGroupOps α] [Mul α] [AddGroupOps β] [Mul β]
  [IsNonUnitalNonAssocRing α] [IsNonUnitalNonAssocRing β]
  : IsNonUnitalNonAssocRing (α × β) where

public instance [AddGroupOps α] [Mul α] [AddGroupOps β] [Mul β]
  [IsNonUnitalRing α] [IsNonUnitalRing β]
  : IsNonUnitalRing (α × β) where

public instance [AddGroupOps α] [Mul α] [One α] [NatCast α] [IntCast α]
  [AddGroupOps β] [Mul β] [One β] [NatCast β][IntCast β]
  [IsNonAssocRing α] [IsNonAssocRing β]
  : IsNonAssocRing (α × β) where

public instance [RingOps α] [RingOps β] [IsRing α] [IsRing β] : IsRing (α × β) where

public instance [∀i, Add (γ i)] [∀i, Mul (γ i)] [∀i, IsLeftDistrib (γ i)] : IsLeftDistrib (∀i, γ i) where
  mul_add _ _ _  := by ext <;> apply mul_add
public instance [∀i, Add (γ i)] [∀i, Mul (γ i)] [∀i, IsRightDistrib (γ i)] : IsRightDistrib (∀i, γ i) where
  add_mul _ _ _  := by ext <;> apply add_mul

public instance [∀i, AddGroupOps (γ i)] [∀i, Mul (γ i)]
  [∀i, IsNonUnitalNonAssocRing (γ i)]
  : IsNonUnitalNonAssocRing (∀i, γ i) where

public instance [∀i, AddGroupOps (γ i)] [∀i, Mul (γ i)]
  [∀i, IsNonUnitalRing (γ i)]
  : IsNonUnitalRing (∀i, γ i) where

public instance [∀i, AddGroupOps (γ i)] [∀i, Mul (γ i)] [∀i, One (γ i)] [∀i, NatCast (γ i)] [∀i, IntCast (γ i)]
  [∀i, IsNonAssocRing (γ i)]
  : IsNonAssocRing (∀i, γ i) where

public instance [∀i, RingOps (γ i)] [∀i, IsRing (γ i)] : IsRing (∀i, γ i) where

public instance [Add α] [Mul α] [IsLeftDistrib α] : IsLeftDistrib (ι -> α)
   := inferInstance
public instance [Add α] [Mul α] [IsRightDistrib α] : IsRightDistrib (ι -> α)
   := inferInstance

public instance [AddGroupOps α] [Mul α] [IsNonUnitalNonAssocRing α]
  : IsNonUnitalNonAssocRing (ι -> α) := inferInstance

public instance [AddGroupOps α] [Mul α] [IsNonUnitalRing α]
  : IsNonUnitalRing (ι -> α) := inferInstance

public instance [AddGroupOps α] [Mul α] [One α] [NatCast α] [IntCast α] [IsNonAssocRing α]
  : IsNonAssocRing (ι -> α) := inferInstance

public instance [RingOps α] [IsRing α] : IsRing (ι -> α) := inferInstance
