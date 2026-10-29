module

public import Math.Data.Equiv.Defs

@[expose] public def AddOfMul (α: Type u) := α
@[expose] public def MulOfAdd (α: Type u) := α

namespace AddOfMul

@[expose] public def mk : α ≃ AddOfMul α := .id _
@[expose] public def get : AddOfMul α ≃ α := .id _

attribute [local irreducible] AddOfMul

public instance [One α] : Zero (AddOfMul α) where
  zero := .mk 1
public instance [Mul α] : Add (AddOfMul α) where
  add a b := .mk (a.get * b.get)
public instance [Pow α β] : SMul β (AddOfMul α) where
  smul a x := .mk (x.get ^ a)
public instance [Div α] : Sub (AddOfMul α) where
  sub a b := .mk (a.get / b.get)
public instance [Inv α] : Neg (AddOfMul α) where
  neg a := .mk (a.get⁻¹)

end AddOfMul

namespace MulOfAdd

@[expose] public def mk : α ≃ MulOfAdd α := .id _
@[expose] public def get : MulOfAdd α ≃ α := .id _

attribute [local irreducible] MulOfAdd

public instance [Zero α] : One (MulOfAdd α) where
  one := .mk 0
public instance [Add α] : Mul (MulOfAdd α) where
  mul a b := .mk (a.get + b.get)
public instance [SMul β α] : Pow (MulOfAdd α) β where
  pow x a := .mk (a • x.get)
public instance [Sub α] : Div (MulOfAdd α) where
  div a b := .mk (a.get - b.get)
public instance [Neg α] : Inv (MulOfAdd α) where
  inv a := .mk (-a.get)

end MulOfAdd
