import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Semiring.Func
import LeanMath.Algebra.AddGroupWithOne.Func

variable {ι: Type*} {A: ι -> Type*} {α: Type*}

instance [∀i, RingOps (A i)] [∀i, IsRing (A i)] : IsRing (∀i, A i) where

instance [RingOps α] [IsRing α] : IsRing (ι -> α) := inferInstance
