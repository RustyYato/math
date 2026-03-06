import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.GroupWithZero.Defs

class SemifieldOps (α: Type*) extends GroupWithZeroOps α, SemiringOps α where

class IsDivisionSemiring (α: Type*) [SemifieldOps α] : Prop extends IsSemiring α, IsGroupWithZero α, NoZeroDivisors α where
class IsSemifield (α: Type*) [SemifieldOps α] : Prop extends IsDivisionSemiring α, IsComm α where
