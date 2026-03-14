import LeanMath.Order.Defs

def Monotone [LE α] [LE β] (f: α -> β) : Prop := ∀⦃a b⦄, a ≤ b -> f a ≤ f b

def Monotone.dual [LE α] [LE β] {f: α -> β} (hf: Monotone f) : Monotone (OrderOpp.mk ∘ f ∘ OrderOpp.get) := by
  intro a b h
  apply hf
  assumption
