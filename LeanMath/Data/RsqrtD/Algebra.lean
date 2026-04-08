import LeanMath.Data.RsqrtD.Module
import LeanMath.Algebra.Algebra.Defs

namespace RsqrtD

variable (r: R)

-- [SemiringOps α] [IsSemiring α] [SemiringOps R] [IsSemiring R] [AlgebraMap R α] [SMul R α] [IsAlgebra R α]

-- instance [SemiringOps α] : MonoidOps (RsqrtD α r) := instMonoidOpsOfOneOfMulOfPowNat
-- instance [SemiringOps α] : SemiringOps (RsqrtD α r) := instSemiringOpsOfAddMonoidWithOneOpsOfMonoidOps

section

variable [SemiringOps S] [SemiringOps α] [IsSemiring α] [SMul R α]
  [IsLawfulSMulZero R α] [IsLawfulZeroAdd α] [IsLawfulZeroMul α]
  [AlgebraMap S α]

instance : AlgebraMap S (RsqrtD α r) where
  toAlgebraMap := {
    toFun s := {
      real := algebraMap S s
      imag := 0
    }
    map_zero := by ext <;> dsimp; rw [map_zero]
    map_one := by ext <;> dsimp; rw [map_one]
    map_add a b := by ext <;> dsimp; rw [map_add]; rw [add_zero]
    map_mul a b := by
      ext <;> dsimp
      rw [map_mul, mul_zero, smul_zero, add_zero]
      rw [mul_zero, zero_mul, add_zero]
  }

@[simp] def algebraMap_real (s: S) : RsqrtD.real (α := α) (r := r) (algebraMap S s) = algebraMap S s := rfl
@[simp] def algebraMap_imag (s: S) : RsqrtD.imag (α := α) (r := r) (algebraMap S s) = 0 := rfl

end

instance
  [SemiringOps α] [IsSemiring α] [SemiringOps R] [IsSemiring R] [AlgebraMap R α] [SMul R α] [IsAlgebra R α]
  [SemiringOps S] [IsSemiring S] [SMul S α] [AlgebraMap S α] [IsAlgebra S α]
  : IsAlgebra S (RsqrtD α r) where
  commutes s x := by
    ext <;> dsimp
    rw [mul_zero, zero_mul, smul_zero, add_zero, add_zero, commutes]
    rw [mul_zero, zero_mul, add_zero, zero_add, commutes]
  smul_def s a := by
    ext <;> dsimp
    rw [zero_mul, smul_zero, add_zero, smul_def]
    rw [zero_mul, add_zero, smul_def]

end RsqrtD
