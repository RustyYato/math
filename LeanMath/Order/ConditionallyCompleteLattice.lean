import LeanMath.Order.Set
import LeanMath.Data.Set.Relation

class IsConditionallyCompleteLattice (α: Type*) [LE α] [LT α] [Min α] [Max α] [InfSet α] [SupSet α] : Prop extends IsLattice α where
  protected le_csSup : ∀{s} {a: α}, s.BoundedAbove → a ∈ s → a ≤ (⨆ s)
  protected csSup_le : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.upperBounds → ⨆ s ≤ a
  protected csInf_le : ∀{s} {a: α}, s.BoundedBelow → a ∈ s → ⨅ s ≤ a
  protected le_csInf : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.lowerBounds → a ≤ ⨅ s

variable [LE α] [LT α] [Min α] [Max α] [InfSet α] [SupSet α] [IsConditionallyCompleteLattice α]

def le_csSup : ∀{s} {a: α}, s.BoundedAbove → a ∈ s → a ≤ (⨆ s) := IsConditionallyCompleteLattice.le_csSup
def csSup_le : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.upperBounds → ⨆ s ≤ a := IsConditionallyCompleteLattice.csSup_le
def csInf_le : ∀{s} {a: α}, s.BoundedBelow → a ∈ s → ⨅ s ≤ a := IsConditionallyCompleteLattice.csInf_le
def le_csInf : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.lowerBounds → a ≤ ⨅ s := IsConditionallyCompleteLattice.le_csInf

instance : IsConditionallyCompleteLattice αᵒᵖ where
  le_csSup := csInf_le (α := α)
  csSup_le := le_csInf (α := α)
  csInf_le := le_csSup (α := α)
  le_csInf := csSup_le (α := α)

def sSup_univ [Top α] [IsLawfulTop α] : ⨆ ⊤ = (⊤: α) := by
  apply le_antisymm (le_top _)
  apply le_csSup
  exists ⊤; intro _ _; apply le_top
  trivial

def sInf_univ [Bot α] [IsLawfulBot α] : ⨅ ⊤ = (⊥: α) :=
  sSup_univ (α := αᵒᵖ)

def csInf_mem [LEM] [IsLinearOrder α] [@Relation.IsWelFounded α (· < ·)]
  {U: Set α} (hU: U.Nonempty) : ⨅ U ∈ U := by
  have : U.BoundedBelow := by
    obtain ⟨x, _⟩ := hU
    have ⟨bot, bot_spec, _⟩ := Relation.exists_unique_min (α := α) (· < ·) (P := fun _ => True) ⟨x, True.intro⟩
    exists bot
    intro x hx
    exact not_lt.mp (bot_spec.right x · True.intro)
  have ⟨u, ⟨umem, hu⟩, _⟩  := Set.exists_unique_min (· < ·) hU
  rwa [show ⨅U = u from ?_]
  apply le_antisymm (csInf_le this umem)
  apply le_csInf
  exists u
  simpa [not_lt] using hu
