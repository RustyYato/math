module

public import Math.Algebra.Monoid.Defs.Prod
public import Math.Algebra.AddMonoidWithOne.Defs.Basic

namespace Math

variable {ι α β: Type*} {γ: ι -> Type*}

public instance [NatCast α] [NatCast β] : NatCast (α × β) where
  natCast n := (n, n)

public instance [Zero α] [Zero β] [One α] [One β] [Add α] [Add β] [NatCast α] [NatCast β] [IsLawfulNatCast α] [IsLawfulNatCast β] : IsLawfulNatCast (α × β) where
  natCast_zero := by ext <;> apply natCast_zero
  natCast_succ _ := by ext <;> apply natCast_succ

public instance [AddMonoidOps α] [AddMonoidOps β] [One α] [One β] [NatCast α] [NatCast β] [IsAddMonoidWithOne α] [IsAddMonoidWithOne β] : IsAddMonoidWithOne (α × β) where

public instance [∀i, NatCast (γ i)] : NatCast (∀i, γ i) where
  natCast n _ := n

public instance [∀i, Zero (γ i)] [∀i, One (γ i)] [∀i, Add (γ i)] [∀i, NatCast (γ i)] [∀i, IsLawfulNatCast (γ i)] : IsLawfulNatCast (∀i, γ i) where
  natCast_zero := by ext <;> apply natCast_zero
  natCast_succ _ := by ext <;> apply natCast_succ

public instance [∀i, AddMonoidOps (γ i)] [∀i, One (γ i)] [∀i, NatCast (γ i)] [∀i, IsAddMonoidWithOne (γ i)] : IsAddMonoidWithOne (∀i, γ i) where

public instance [NatCast α] : NatCast (ι -> α) := inferInstance
public instance [Zero α] [One α] [Add α] [NatCast α] [IsLawfulNatCast α] : IsLawfulNatCast (ι -> α) := inferInstance
public instance [AddMonoidOps α] [One α] [NatCast α] [IsAddMonoidWithOne α] : IsAddMonoidWithOne (ι -> α) := inferInstance
