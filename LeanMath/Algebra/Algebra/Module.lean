import LeanMath.Algebra.Algebra.Defs
import LeanMath.Algebra.Module.Defs

variable [SemiringOps R] [SemiringOps α]
  [AlgebraMap R α] [IsSemiring R] [IsSemiring α]
  [SMul R α] [IsAlgebra R α]

-- every algebra is also a module
instance : IsModule R α where
  one_smul a := by rw [smul_def, map_one, one_mul]
  mul_smul r s a := by rw [smul_def, smul_def, smul_def, map_mul, mul_assoc]
  smul_zero r := by rw [smul_def, mul_zero]
  smul_add r a b := by rw [smul_def, smul_def, smul_def, mul_add]
  add_smul r s a := by rw [smul_def, smul_def, smul_def, map_add, add_mul]
