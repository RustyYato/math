module

public import Math.Algebra.AddMonoidWithOne.Congruence
public import Math.Algebra.MonoidWithZero.Congruence
public import Math.Algebra.Semiring.Defs.Hom

namespace Math

variable [RelLike C α] [IsCon C α]

public instance [Add α] [Mul α] [IsLeftDistrib α] [IsAddCon C α] [IsMulCon C α] (r: C) : IsLeftDistrib (AlgQuot r) where
  mul_add k a b := by
    induction k
    induction a
    induction b
    show AlgQuot.mk _ _=  AlgQuot.mk _ _
    rw [mul_add]
public instance [Add α] [Mul α] [IsRightDistrib α] [IsAddCon C α] [IsMulCon C α] (r: C) : IsRightDistrib (AlgQuot r) where
  add_mul a b k := by
    induction a
    induction b
    induction k
    show AlgQuot.mk _ _=  AlgQuot.mk _ _
    rw [add_mul]
public instance [SemiringOps α] [IsSemiring α] [IsAddCon C α] [IsMulCon C α] (r: C) : IsSemiring (AlgQuot r) where
