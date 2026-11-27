module

public import Math.Algebra.AddMonoidWithOne.Congruence
public import Math.Algebra.Group.Congruence
public import Math.Algebra.AddGroupWithOne.Defs.Hom

namespace Math

variable [RelLike C α] [IsCon C α]

public instance [AddGroupOps α] [One α] [NatCast α] [IntCast α] [IsAddGroupWithOne α] [IsAddCon C α] (r: C) : IsAddGroupWithOne (AlgQuot r) where
  intCast_ofNat n := by
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [intCast_ofNat]
  intCast_negSucc n := by
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [intCast_negSucc]
