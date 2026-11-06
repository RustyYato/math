module

public import Math.Data.Set.Defs
public import Math.Order.Opposite
public import Math.Data.Set.Nonempty

@[expose] section
namespace Math.Set

variable [LE α] [LT α]

public def upperBounds (U: Set α) : Set α where
  Mem a := ∀u ∈ U, u ≤ a
public def lowerBounds (U: Set α) : Set α where
  Mem a := ∀u ∈ U, a ≤ u

public def boundedAbove (U: Set α) := (upperBounds U).Nonempty
public def boundedBelow (U: Set α) := (lowerBounds U).Nonempty

public def isMax (a: α) (U: Set α) := a ∈ U ∩ U.upperBounds
public def isMin (a: α) (U: Set α) := a ∈ U ∩ U.lowerBounds

public def isGLB (a: α) (U: Set α) := U.lowerBounds.isMax a
public def isLUB (a: α) (U: Set α) := U.upperBounds.isMin a

public def Iio (a: α) : Set α where
  Mem x := x < a
public def Ioi (a: α) : Set α where
  Mem x := a < x
public def Iic (a: α) : Set α where
  Mem x := x ≤ a
public def Ici (a: α) : Set α where
  Mem x := a ≤ x
public def Ioo (a b: α) : Set α := Ioi a ∩ Iio b
public def Ioc (a b: α) : Set α := Ioi a ∩ Iic b
public def Ico (a b: α) : Set α := Ici a ∩ Iio b
public def Icc (a b: α) : Set α := Ici a ∩ Iic b

attribute [local irreducible] OrderOpp

public instance [InfSet α] : SupSet αᵒᵖ where
  sSup U := .mk (⨅ (U.preimage .mk))
public instance [SupSet α] : InfSet αᵒᵖ where
  sInf U := .mk (⨆ (U.preimage .mk))
