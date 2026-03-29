import LeanMath.Order.Defs
import LeanMath.Data.Set.Defs

class IsCompleteSemilatticeSup (α: Type*) [LE α] [LT α] [Max α] [SupSet α] [Top α] [Bot α] : Prop extends IsSemiLatticeMax α, IsLawfulSup α, IsLawfulTop α, IsLawfulBot α where
  protected sSup_le (U: Set α) (x: α) : (∀u ∈ U, u ≤ x) -> ⨆ U ≤ x

class IsCompleteSemilatticeInf (α: Type*) [LE α] [LT α] [Min α] [InfSet α] [Top α] [Bot α] : Prop extends IsSemiLatticeMin α, IsLawfulInf α, IsLawfulTop α, IsLawfulBot α where
  protected le_sInf (U: Set α) (x: α) : (∀u ∈ U, x ≤ u) -> x ≤ ⨅ U

class IsCompleteLattice (α: Type*) [LE α] [LT α] [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α] : Prop extends IsCompleteSemilatticeInf α, IsCompleteSemilatticeSup α, IsLattice α, IsLawfulTop α, IsLawfulBot α where

section

variable [LE α] [LT α] [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α]

def sSup_le [IsCompleteSemilatticeSup α] (U: Set α) (x: α) : (∀u ∈ U, u ≤ x) -> ⨆ U ≤ x :=
  IsCompleteSemilatticeSup.sSup_le _ _

def le_sInf [IsCompleteSemilatticeInf α] (U: Set α) (x: α) : (∀u ∈ U, x ≤ u) -> x ≤ ⨅ U :=
  IsCompleteSemilatticeInf.le_sInf _ _

end

section IsCompleteSemilatticeSup

variable [LE α] [LT α] [Max α] [SupSet α] [Top α] [Bot α] [IsCompleteSemilatticeSup α]

def sSup_empty : ⨆ ⊥ = (⊥: α) := by
  apply le_antisymm _ (bot_le _)
  apply sSup_le
  intro u hu; contradiction

def sSup_univ : ⨆ ⊤ = (⊤: α) := by
  apply le_antisymm (le_top _)
  apply le_sSup
  trivial

end IsCompleteSemilatticeSup

section IsCompleteSemilatticeInf

variable [LE α] [LT α] [Min α] [InfSet α] [Top α] [Bot α] [IsCompleteSemilatticeInf α]

def sInf_empty : ⨅ ⊥ = (⊤: α) := by
  apply le_antisymm (le_top _)
  apply le_sInf
  intro u hu; contradiction

def sInf_univ : ⨅ ⊤ = (⊥: α) := by
  apply le_antisymm _ (bot_le _)
  apply sInf_le
  trivial

end IsCompleteSemilatticeInf
