module

public import Math.Algebra.Semigroup.Defs
public import Math.Algebra.Congruence.Defs

namespace Math

variable [RelLike C α] [IsCon C α]

public instance [Mul α] [IsSemigroup α] [IsMulCon C α] (r: C) : IsSemigroup (AlgQuot r) where
  mul_assoc a b c := by
    induction a
    induction b
    induction c
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [mul_assoc]

public instance [Mul α] [IsComm α] [IsMulCon C α] (r: C) : IsComm (AlgQuot r) where
  mul_comm a b := by
    induction a
    induction b
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [mul_comm]

public instance [Add α] [IsAddSemigroup α] [IsAddCon C α] (r: C) : IsAddSemigroup (AlgQuot r) where
  add_assoc a b c := by
    induction a
    induction b
    induction c
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [add_assoc]

public instance [Add α] [IsAddComm α] [IsAddCon C α] (r: C) : IsAddComm (AlgQuot r) where
  add_comm a b := by
    induction a
    induction b
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [add_comm]
