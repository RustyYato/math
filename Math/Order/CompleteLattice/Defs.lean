module

public import Math.Order.Set
public import Math.Order.Monotone

namespace Math

section Property

public class SupLatticeOps (α: Type*) extends SupSemilatticeOps α, SupSet α where
public class InfLatticeOps (α: Type*) extends InfSemilatticeOps α, InfSet α where
public class CompleteLatticeOps (α: Type*) extends LatticeOps α, SupLatticeOps α, InfLatticeOps α, Top α, Bot α where

public instance [SupSemilatticeOps α] [SupSet α] : SupLatticeOps α where
public instance [InfSemilatticeOps α] [InfSet α] : InfLatticeOps α where
public instance [SupSet α] [Max α] [Top α] [InfSet α] [Min α] [Bot α] [LE α] [LT α] : CompleteLatticeOps α where

public class IsSupLattice (α: Type*) [SupLatticeOps α] extends IsLawfulSup α, IsSupSemilattice α where
  sSup_le (U: Set α) : ⨆ U ∈ U.upperBounds.lowerBounds
public class IsInfLattice (α: Type*) [InfLatticeOps α] extends IsLawfulInf α, IsInfSemilattice α where
  le_sInf (U: Set α) : ⨅ U ∈ U.lowerBounds.upperBounds
public class IsCompleteLattice (α: Type*) [CompleteLatticeOps α] extends
    IsSupLattice α, IsLawfulMax α, IsLawfulTop α,
    IsInfLattice α, IsLawfulMin α, IsLawfulBot α where

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

section SupLattice

public theorem sSup_bot [SupLatticeOps α] [IsSupLattice α] [Bot α] [IsLawfulBot α] : ⨆ ⊥ = (⊥: α) := by
  apply le_antisymm
  apply sSup_le _ _ nofun
  apply bot_le

public theorem sSup_top [LE α] [LT α] [SupSet α] [Top α] [IsPartialOrder α] [IsLawfulSup α] [IsLawfulTop α] : ⨆ ⊤ = (⊤: α) := by
  apply le_antisymm
  apply le_top
  apply le_sSup
  trivial

public theorem sSup_monotone [SupLatticeOps α] [IsSupLattice α] : IsMonotone (fun x: Set α => ⨆ x) := by
  intro a b a_le_b; dsimp
  apply sSup_le
  intro x hx
  apply le_sSup
  apply a_le_b
  assumption

public theorem sSup_isLUB [SupLatticeOps α] [IsSupLattice α] (U: Set α) : U.isLUB (⨆ U) := by
  apply And.intro
  apply le_sSup
  apply sSup_le

end SupLattice

section InfLattice

public theorem sInf_bot [InfLatticeOps α] [Top α] [IsInfLattice α] [IsLawfulTop α] : ⨅ ⊥ = (⊤: α) :=
  sSup_bot (α := αᵒᵖ)

public theorem sInf_top [LE α] [LT α] [InfSet α] [Bot α] [IsPartialOrder α] [IsLawfulInf α] [IsLawfulBot α] : ⨅ ⊤ = (⊥: α) :=
  sSup_top (α := αᵒᵖ)

public theorem sInf_antitone [InfLatticeOps α] [IsInfLattice α] : IsAntitone (fun x: Set α => ⨅ x) :=
  sSup_monotone (α := αᵒᵖ)

public theorem sInf_isGLB [InfLatticeOps α] [IsInfLattice α] (U: Set α) : U.isGLB (⨅ U) :=
  sSup_isLUB (α := αᵒᵖ) U

end InfLattice
