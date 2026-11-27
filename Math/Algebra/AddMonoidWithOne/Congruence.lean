module

public import Math.Algebra.Monoid.Congruence
public import Math.Algebra.AddMonoidWithOne.Defs.Basic

namespace Math

variable [RelLike C α] [IsCon C α]

public instance [AddMonoidOps α] [One α] [NatCast α] [IsAddMonoidWithOne α] [IsAddCon C α] (r: C) : IsAddMonoidWithOne (AlgQuot r) where
  natCast_zero := by
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [natCast_zero]
  natCast_succ n := by
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [natCast_succ]
