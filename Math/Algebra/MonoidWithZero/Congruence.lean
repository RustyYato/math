module

public import Math.Algebra.Monoid.Congruence
public import Math.Algebra.MonoidWithZero.Defs.Hom

namespace Math

variable [RelLike C α] [IsCon C α]

public instance [Mul α] [Zero α] [IsLawfulZeroMul α] [IsMulCon C α] (r: C) : IsLawfulZeroMul (AlgQuot r) where
  mul_zero a := by induction a with | _ a => show AlgQuot.mk _ _ = AlgQuot.mk _ _; rw [mul_zero]
  zero_mul a := by induction a with | _ a => show AlgQuot.mk _ _ = AlgQuot.mk _ _; rw [zero_mul]

public instance [MonoidOps α] [Zero α] [IsMonoidWithZero α] [IsMulCon C α] (r: C) : IsMonoidWithZero (AlgQuot r) where
