import LeanMath.Algebra.MonoidWithZero.Order
import LeanMath.Algebra.Semiring.Defs

class IsOrderedNonUnitalNonAssocSemiring (α: Type*) [LT α] [LE α] [AddMonoidOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsOrderedAddCommMonoid α, IsOrderedZeroMul α where

class IsOrderedSemiring (α: Type*) [LT α] [LE α] [SemiringOps α] extends IsSemiring α, IsOrderedNonUnitalNonAssocSemiring α where

class IsStrictOrderedNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] [LT α] [LE α] extends IsOrderedNonUnitalNonAssocSemiring α where
  mul_pos: ∀{a b: α}, 0 < a -> 0 < b -> 0 < a * b

class IsStrictOrderedSemiring (α: Type*) [SemiringOps α] [LT α] [LE α] extends
  IsOrderedSemiring α, IsStrictOrderedNonUnitalNonAssocSemiring α where

instance : IsStrictOrderedSemiring ℕ where
  mul_pos := Nat.mul_pos

instance : IsStrictOrderedSemiring ℤ where
  mul_pos := Int.mul_pos
