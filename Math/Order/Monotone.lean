module

public import Math.Order.Defs

namespace Math

@[expose] section

public def IsMonotone [LE α] [LE β] (f: α -> β) : Prop := ∀a b, a ≤ b -> f a ≤ f b
public def IsAntitone [LE α] [LE β] (f: α -> β) : Prop := ∀a b, a ≤ b -> f b ≤ f a

public def IsStrictMonotone [LT α] [LT β] (f: α -> β) : Prop := ∀a b, a < b -> f a < f b
public def IsStrictAntitone [LT α] [LT β] (f: α -> β) : Prop := ∀a b, a < b -> f b < f a
