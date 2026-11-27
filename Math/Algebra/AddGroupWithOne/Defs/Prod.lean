module

public import Math.Algebra.Group.Defs.Prod
public import Math.Algebra.AddMonoidWithOne.Defs.Prod
public import Math.Algebra.AddGroupWithOne.Defs.Basic

namespace Math

variable {ι α β: Type*} {γ: ι -> Type*}

public instance [IntCast α] [IntCast β] : IntCast (α × β) where
  intCast n := (n, n)

public instance [Neg α] [Neg β] [NatCast α] [NatCast β] [IntCast α] [IntCast β] [IsLawfulIntCast α] [IsLawfulIntCast β] : IsLawfulIntCast (α × β) where
  intCast_ofNat n := by ext <;> apply intCast_ofNat
  intCast_negSucc n := by ext <;> apply intCast_negSucc

public instance [AddGroupOps α] [AddGroupOps β] [One α] [One β] [NatCast α] [NatCast β] [IntCast α] [IntCast β] [IsAddGroupWithOne α] [IsAddGroupWithOne β] : IsAddGroupWithOne (α × β) where

public instance [∀i, IntCast (γ i)] : IntCast (∀i, γ i) where
  intCast n _ := n

public instance [∀i, Neg (γ i)] [∀i, NatCast (γ i)] [∀i, IntCast (γ i)] [∀i, IsLawfulIntCast (γ i)] : IsLawfulIntCast (∀i, γ i) where
  intCast_ofNat n := by ext <;> apply intCast_ofNat
  intCast_negSucc n := by ext <;> apply intCast_negSucc

public instance [∀i, AddGroupOps (γ i)] [∀i, One (γ i)] [∀i, NatCast (γ i)] [∀i, IntCast (γ i)] [∀i, IsAddGroupWithOne (γ i)] : IsAddGroupWithOne (∀i, γ i) where

public instance [IntCast α] : IntCast (ι -> α) := inferInstance
public instance [Neg α] [NatCast α] [IntCast α] [IsLawfulIntCast α] : IsLawfulIntCast (ι -> α) := inferInstance
public instance [AddGroupOps α] [One α] [NatCast α] [IntCast α] [IsAddGroupWithOne α] : IsAddGroupWithOne (ι -> α) := inferInstance
