import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Algebra.Defs

variable [RingOps α] [IsRing α]

instance : AlgebraMap ℤ α where
  toAlgebraMap := intCastHom
instance : IsAlgebra ℤ α where
  smul_def n a := by rw [zsmul_eq_intCast_mul]; rfl
  commutes n a := by
    show n * a = a * n
    rw [mul_comm]
