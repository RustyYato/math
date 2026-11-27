module

public import Math.Algebra.GroupWithZero.Defs.Basic
public import Math.Algebra.Semiring.Defs.Basic

namespace Math

public class SemifieldOps (α: Type*) extends
  SemiringOps α, GroupWithZeroOps α where

public instance
  [SemiringOps α] [CheckedInv? α]
  [CheckedDiv? α] [CheckedZPow? α]
   : SemifieldOps α where

public class IsDivisionSemiring (α: Type*) [SemifieldOps α] extends
  IsSemiring α, IsGroupWithZero α, NoZeroDivisors α where
public class IsSemifield (α: Type*) [SemifieldOps α] extends
  IsDivisionSemiring α, IsComm α where
