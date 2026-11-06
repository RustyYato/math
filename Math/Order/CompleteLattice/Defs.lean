module

public import Math.Order.Set
public import Math.Order.Defs

namespace Math

section Property

public class IsSupLattice (α: Type*) [SupSet α] [Max α] [LE α] [LT α] extends IsLawfulSup α, IsSemiSupLattice α where
  sSup_le (U: Set α) : ⨆ U ∈ U.upperBounds.lowerBounds
public class IsInfLattice (α: Type*) [InfSet α] [Min α] [LE α] [LT α] extends IsLawfulInf α, IsSemiInfLattice α where
  le_sInf (U: Set α) : ⨅ U ∈ U.lowerBounds.upperBounds
public class IsCompleteLattice (α: Type*)
  [SupSet α] [Max α] [Top α]
  [InfSet α] [Min α] [Bot α]
  [LE α] [LT α] extends
    IsSupLattice α, IsLawfulMax α,
    IsInfLattice α, IsLawfulMin α where

export IsSupLattice (sSup_le)
export IsInfLattice (le_sInf)

end Property

section Opposite

instance [InfSet α] [Min α] [LE α] [LT α] [IsInfLattice α] : IsSupLattice αᵒᵖ where
  sSup_le := le_sInf (α := α)
instance [SupSet α] [Max α] [LE α] [LT α] [IsSupLattice α] : IsInfLattice αᵒᵖ where
  le_sInf := sSup_le (α := α)
instance [SupSet α] [Max α] [Top α]
  [InfSet α] [Min α] [Bot α]
  [LE α] [LT α] [IsCompleteLattice α] : IsCompleteLattice αᵒᵖ where
  le_sInf := sSup_le (α := α)

end Opposite
