import LeanMath.Algebra.AddGroupWithOne.Defs
import LeanMath.Algebra.AddMonoidWithOne.Func
import LeanMath.Algebra.Group.Func

variable {ι: Type*} {A: ι -> Type*} {α: Type*}

instance [∀i, IntCast (A i)] : IntCast (∀i, A i) where
  intCast n _ := n

instance [IntCast α] : IntCast (ι -> α) := inferInstance

@[simp] def Function.apply_intCast [∀i, IntCast (A i)] (n: ℤ) (i: ι) : (n: ∀i, A i) i = (n: A i) := rfl

instance [∀i, NatCast (A i)] [∀i, IntCast (A i)] [∀i, Neg (A i)] [∀i, IsLawfulIntCast (A i)] : IsLawfulIntCast (∀i, A i) where
  intCast_ofNat _ := by ext; apply intCast_ofNat
  intCast_negSucc _ := by ext; apply intCast_negSucc

instance [∀i, AddGroupWithOneOps (A i)] [∀i, IsAddGroupWithOne (A i)] : IsAddGroupWithOne (∀i, A i) where

instance [NatCast α] [IntCast α] [Neg α] [IsLawfulIntCast α] : IsLawfulIntCast (ι -> α) := inferInstance
instance [AddGroupWithOneOps α] [IsAddGroupWithOne α] : IsAddGroupWithOne (ι -> α) := inferInstance
