module

public import Math.Order.Defs

namespace Math

@[expose] section

public def IsMonotone [LE α] [LE β] (f: α -> β) : Prop := ∀a b, a ≤ b -> f a ≤ f b
public def IsAntitone [LE α] [LE β] (f: α -> β) : Prop := ∀a b, a ≤ b -> f b ≤ f a

public def IsStrictMonotone [LT α] [LT β] (f: α -> β) : Prop := ∀a b, a < b -> f a < f b
public def IsStrictAntitone [LT α] [LT β] (f: α -> β) : Prop := ∀a b, a < b -> f b < f a

public theorem IsMonotone.dual [LE α] [LE β] (f: α -> β) : IsMonotone f -> IsMonotone (OrderOpp.mk ∘ f ∘ OrderOpp.get) := by
  intro m a b h
  dsimp
  show f b.get ≤ f a.get
  apply m
  assumption
