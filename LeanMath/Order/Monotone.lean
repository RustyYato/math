import LeanMath.Order.Defs

def Monotone [LE α] [LE β] (f: α -> β) : Prop := ∀⦃a b⦄, a ≤ b -> f a ≤ f b

def Monotone.dual [LE α] [LE β] {f: α -> β} (hf: Monotone f) : Monotone (OrderOpp.mk ∘ f ∘ OrderOpp.get) := by
  intro a b h
  apply hf
  assumption

def StrictMonotone [LT α] [LT β] (f: α -> β) : Prop := ∀⦃a b⦄, a < b -> f a < f b

def StrictMonotone.dual [LT α] [LT β] {f: α -> β} (hf: StrictMonotone f) : StrictMonotone (OrderOpp.mk ∘ f ∘ OrderOpp.get) := by
  intro a b h
  apply hf
  assumption

def StrictMonotone.le_iff_le [LE α] [LT α] [LE β] [LT β] [IsLinearOrder α] [IsPreorder β] {f: α -> β} (hf : StrictMonotone f) {a b : α} : f a ≤ f b ↔ a ≤ b := by
  apply Iff.intro
  · intro h
    apply not_lt.mp
    intro g
    exact not_le_of_lt (hf g) h
  · intro h; rcases lt_or_eq_of_le h with h | rfl
    apply le_of_lt; apply hf; assumption
    rfl

def StrictMonotone.inj [LT α] [LT β] [LE β] [IsPreorder β] [IsLTTrichotomous α] (f: α -> β) (hf: StrictMonotone f) : Function.Injective f := by
  intro a b h
  rcases lt_trichotomy a b with g | g | g
  nomatch Relation.irrefl (h ▸ hf g)
  assumption
  nomatch Relation.irrefl (h ▸ hf g)
