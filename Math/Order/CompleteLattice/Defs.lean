module

public import Math.Order.Set
public import Math.Order.Defs

namespace Math

section Property

public class SupLatticeOps (α: Type*) extends SemiSupLatticeOps α, SupSet α where
public class InfLatticeOps (α: Type*) extends SemiInfLatticeOps α, InfSet α where
public class CompleteLatticeOps (α: Type*) extends LatticeOps α, SupLatticeOps α, InfLatticeOps α, Top α, Bot α where

public instance [SemiSupLatticeOps α] [SupSet α] : SupLatticeOps α where
public instance [SemiInfLatticeOps α] [InfSet α] : InfLatticeOps α where
public instance [SupSet α] [Max α] [Top α] [InfSet α] [Min α] [Bot α] [LE α] [LT α] : CompleteLatticeOps α where

public class IsSupLattice (α: Type*) [SupLatticeOps α] extends IsLawfulSup α, IsSemiSupLattice α where
  sSup_le (U: Set α) : ⨆ U ∈ U.upperBounds.lowerBounds
public class IsInfLattice (α: Type*) [InfLatticeOps α] extends IsLawfulInf α, IsSemiInfLattice α where
  le_sInf (U: Set α) : ⨅ U ∈ U.lowerBounds.upperBounds
public class IsCompleteLattice (α: Type*) [CompleteLatticeOps α] extends
    IsSupLattice α, IsLawfulMax α,
    IsInfLattice α, IsLawfulMin α where

export IsSupLattice (sSup_le)
export IsInfLattice (le_sInf)

end Property

section Basic

public instance [InfLatticeOps α] [IsInfLattice α] : IsSupLattice αᵒᵖ where
  sSup_le := le_sInf (α := α)
public instance [SupLatticeOps α] [IsSupLattice α] : IsInfLattice αᵒᵖ where
  le_sInf := sSup_le (α := α)
public instance [CompleteLatticeOps α] [IsCompleteLattice α] : IsCompleteLattice αᵒᵖ where
  le_sInf := sSup_le (α := α)

public instance : IsCompleteLattice (Set α) where
  sSup_le U u hu x hx := by
    obtain ⟨_, _, _⟩ := hx
    apply hu; assumption; assumption
  le_sInf U u hu x hx := by
    intro s hs
    apply hu; assumption; assumption

end Basic
