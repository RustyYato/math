import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Semifield.Defs

class FieldOps (α: Type*) extends SemifieldOps α, RingOps α where

class IsDivisionRing (α: Type*) [FieldOps α] : Prop extends IsDivisionSemiring α, IsRing α where
class IsField (α: Type*) [FieldOps α] : Prop extends IsDivisionRing α, IsSemifield α where
