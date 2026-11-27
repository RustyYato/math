module

public import Math.Algebra.Monoid.Defs.Basic

namespace Math

section Property

public class IsLawfulNatCast (α: Type*) [Add α] [Zero α] [One α] [NatCast α] where
  natCast_zero : ((0: ℕ): α) = 0
  natCast_succ (n: ℕ) : ((n + 1: ℕ): α) = n + 1

export IsLawfulNatCast (natCast_zero natCast_succ)

public class IsAddMonoidWithOne (α: Type*) [AddMonoidOps α] [One α] [NatCast α] extends IsAddMonoid α, IsLawfulNatCast α where

end Property

section Basic

public instance : IsAddMonoidWithOne ℕ where
  natCast_zero := rfl
  natCast_succ _ := rfl
public instance : IsAddMonoidWithOne ℤ where
  natCast_zero := rfl
  natCast_succ _ := rfl

end Basic
