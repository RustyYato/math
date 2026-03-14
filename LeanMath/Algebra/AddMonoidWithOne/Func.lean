import LeanMath.Algebra.AddMonoidWithOne.Defs
import LeanMath.Algebra.Monoid.Func

variable {ι: Type*} {A: ι -> Type*} {α: Type*}

instance [∀i, NatCast (A i)] : NatCast (∀i, A i) where
  natCast n _ := n

instance [NatCast α] : NatCast (ι -> α) := inferInstance

@[simp] def Function.apply_natCast [∀i, NatCast (A i)] (n: ℕ) (i: ι) : (n: ∀i, A i) i = (n: A i) := rfl

instance [∀i, NatCast (A i)] [∀i, Zero (A i)] [∀i, One (A i)] [∀i, Add (A i)] [∀i, IsLawfulNatCast (A i)] : IsLawfulNatCast (∀i, A i) where
  natCast_zero := by ext; apply natCast_zero
  natCast_one := by ext; apply natCast_one
  natCast_succ _ := by ext; apply natCast_succ

instance [∀i, AddMonoidWithOneOps (A i)] [∀i, IsAddMonoidWithOne (A i)] : IsAddMonoidWithOne (∀i, A i) where

instance [NatCast α] [Zero α] [One α] [Add α] [IsLawfulNatCast α] : IsLawfulNatCast (ι -> α) := inferInstance
instance [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] : IsAddMonoidWithOne (ι -> α) := inferInstance
