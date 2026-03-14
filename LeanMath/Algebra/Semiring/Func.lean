import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.AddMonoidWithOne.Func

variable {ι: Type*} {A: ι -> Type*} {α: Type*}

instance [∀i, Add (A i)] [∀i, Mul (A i)] [∀i, IsLeftDistrib (A i)] : IsLeftDistrib (∀i, A i) where
  mul_add _ _ _ := by ext; apply mul_add
instance [∀i, Add (A i)] [∀i, Mul (A i)] [∀i, IsRightDistrib (A i)] : IsRightDistrib (∀i, A i) where
  add_mul _ _ _ := by ext; apply add_mul

instance [∀i, SemiringOps (A i)] [∀i, IsSemiring (A i)] : IsSemiring (∀i, A i) where

instance [Add α] [Mul α] [IsLeftDistrib α] : IsLeftDistrib (ι -> α) := inferInstance
instance [Add α] [Mul α] [IsRightDistrib α] : IsRightDistrib (ι -> α) := inferInstance
instance [SemiringOps α] [IsSemiring α] : IsSemiring (ι -> α) := inferInstance
