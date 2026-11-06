module

public import Math.Order.Relation.Defs
public import Math.Data.OfEquiv.Defs
public import Math.Order.Opposite
public import Math.Tactic.Basic

namespace Math

public class IsLawfulLT (α: Type*) [LE α] [LT α] where
  lt_iff_le_and_not_ge (a b: α) : a < b ↔ a ≤ b ∧ ¬(b ≤ a)
export IsLawfulLT (lt_iff_le_and_not_ge)
public class IsPreOrder (α: Type*) [LE α] [LT α] extends IsLawfulLT α, IsRefl (α := α) (· ≤ ·), IsTrans (α := α) (· ≤ ·) where
public class IsPartialOrder (α: Type*) [LE α] [LT α] extends IsAntisymm (α := α) (· ≤ ·) (· = ·) where
public class IsLinearOrder (α: Type*) [LE α] [LT α] extends IsPartialOrder α, IsConnected (α := α) (· ≤ ·) (· = ·) where

infixl:68 " ⊔ " => max
infixl:69 " ⊓ " => min

public class IsLawfulMax (α: Type*) [Max α] [LE α] where
  left_le_max (a b: α) : a ≤ a ⊔ b
  right_le_max (a b: α) : b ≤ a ⊔ b
public class IsLawfulMin (α: Type*) [Min α] [LE α] where
  min_le_left (a b: α) : a ⊓ b ≤ a
  min_le_right (a b: α) : a ⊓ b ≤ b

export IsLawfulMax (left_le_max right_le_max)
export IsLawfulMin (min_le_left min_le_right)

public class IsSemiSupLattice (α: Type*) [Max α] [LE α] [LT α] extends IsPartialOrder α, IsLawfulMax α where
  max_le (k a b: α) : a ≤ k -> b ≤ k -> a ⊔ b ≤ k
public class IsSemiInfLattice (α: Type*) [Min α] [LE α] [LT α] extends IsPartialOrder α, IsLawfulMin α where
  le_min (k a b: α) : k ≤ a -> k ≤ b -> k ≤ a ⊓ b

export IsSemiSupLattice (max_le)
export IsSemiInfLattice (le_min)

public class IsLattice (α: Type*) [Max α] [Min α] [LE α] [LT α] extends IsSemiSupLattice α, IsSemiInfLattice α where
