module

public import Math.Algebra.Semiring.Congruence
public import Math.Algebra.AddGroupWithOne.Congruence
public import Math.Algebra.Ring.Defs

namespace Math

variable [RelLike C α] [IsCon C α]

public instance [RingOps α] [IsRing α] [IsAddCon C α] [IsMulCon C α] (r: C) : RingOps (AlgQuot r) :=
  instRingOps

public instance [RingOps α] [IsRing α] [IsAddCon C α] [IsMulCon C α] (r: C) : IsRing (AlgQuot r) where
