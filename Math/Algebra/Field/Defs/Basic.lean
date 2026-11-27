module

public import Math.Algebra.Semifield.Defs.Basic
public import Math.Algebra.Ring.Defs.Basic

namespace Math

public class FieldOps (α: Type*) extends SemifieldOps α, RingOps α where

public instance
  [RingOps α] [CheckedInv? α]
  [CheckedDiv? α] [CheckedZPow? α]
   : FieldOps α where

public class IsDivisionRing (α: Type*) [FieldOps α] extends
  IsDivisionSemiring α, IsRing α where
public class IsField (α: Type*) [FieldOps α] extends
  IsDivisionRing α, IsSemifield α where
