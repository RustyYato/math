import LeanMath.Algebra.Semiring.Ideal.TwoSided.Defs
import LeanMath.Algebra.Group.Set
import LeanMath.Algebra.Ring.Defs

variable [RingOps α] [IsRing α]

instance : IsMemNeg (Ideal α) α where
  mem_neg s {a} h := by
    rw [←one_mul a, neg_mul_left]
    apply mem_left_mul
    assumption
