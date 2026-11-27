module

public import Math.Algebra.AddGroupWithOne.Defs.Basic
public import Math.Algebra.Semiring.Defs.Basic

namespace Math

section Property

public class RingOps (α: Type*)
  extends AddGroupOps α, SemiringOps α, IntCast α where

public instance instRingOps [AddGroupOps α] [MonoidOps α] [NatCast α] [IntCast α] : RingOps α where

public class IsNonUnitalNonAssocRing (α: Type*)
  [AddGroupOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsAddGroup α, IsLeftDistrib α, IsRightDistrib α, IsLawfulZeroMul α, IsAddComm α  where

public class IsNonUnitalRing (α: Type*)
  [AddGroupOps α] [Mul α] extends IsNonUnitalSemiring α, IsNonUnitalNonAssocRing α, IsSemigroup α where

public class IsNonAssocRing (α: Type*)
  [AddGroupOps α] [One α] [Mul α] [NatCast α] [IntCast α] extends IsNonAssocSemiring α, IsNonUnitalNonAssocRing α, IsAddGroupWithOne α, IsLawfulOne α where

public class IsRing (α: Type*) [RingOps α] : Prop extends IsAddGroup α, IsSemiring α, IsNonUnitalRing α, IsNonAssocRing α, IsMonoidWithZero α where

-- shortcut instance, since Lean is too stupid to do this sometimes and goes on a wild goose chase
-- through other irrelevant instances
public instance [RingOps α] [IsRing α] : IsAddGroup α := inferInstance

end Property

section Basics

public instance : IsRing ℤ where
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

end Basics
