import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Algebra.Semiring.Defs

class IsModule (R α: Type*)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  [SMul R α]
  : Prop extends IsDistributiveAction R α, IsLeftDistribSMul R α, IsLawfulZeroSMul R α where

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsModule ℕ α where

variable [SemiringOps R] [IsSemiring R] [Add α] [SMul R α] [AddMonoidOps β] [IsAddMonoid β]
  [IsAddComm β] [SMul R β] [IsSMulComm R R β] [IsModule R β]

instance : IsModule R (α →ₗ[R] β) where
  add_smul _ _ _ := by
    apply DFunLike.ext; intro x
    apply add_smul
  zero_smul _ := by
    apply DFunLike.ext; intro x
    apply zero_smul

instance : IsModule R R where
  one_smul := one_mul
  mul_smul := mul_assoc
  smul_zero := mul_zero
  smul_add := mul_add
  add_smul := add_mul
  zero_smul := zero_mul

instance : IsScalarTower ℕ R β where
  smul_assoc n r a := by
    induction n with
    | zero => simp [zero_smul]
    | succ n ih => rw [succ_nsmul, succ_nsmul, add_smul, ih]

namespace OfEquiv

variable {R S α β: Type*} (f: α ≃ β)

protected scoped instance [SemiringOps R] [IsSemiring R] [AddMonoidOps β] [IsAddMonoid β] [IsAddComm β] [SMul R β] [IsModule R β] : IsModule R (OfEquiv f) where

end OfEquiv
