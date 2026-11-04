module

public import Math.Data.Equiv.Defs

@[expose] public def AddOfMul (α: Type u) := α
@[expose] public def MulOfAdd (α: Type u) := α
@[expose] public def MulOpp (α: Type u) := α
@[expose] public def AddOpp (α: Type u) := α

postfix:max "ᵐᵒᵖ" => MulOpp
postfix:max "ᵃᵒᵖ" => AddOpp

namespace AddOfMul

@[expose] public def mk : α -> AddOfMul α := id
@[expose] public def get : AddOfMul α -> α := id

@[simp] public theorem mk_get (a: AddOfMul α) : .mk a.get = a := rfl
@[simp] public theorem get_mk (a: α) : get (.mk a) = a := rfl

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

@[expose] public def mk : α -> MulOfAdd α := id
@[expose] public def get : MulOfAdd α -> α := id

@[simp] public theorem mk_get (a: MulOfAdd α) : .mk a.get = a := rfl
@[simp] public theorem get_mk (a: α) : get (.mk a) = a := rfl

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

namespace MulOpp

@[expose] public def mk : α -> αᵐᵒᵖ := id
@[expose] public def get : αᵐᵒᵖ -> α := id

@[simp] public theorem mk_get (a: αᵐᵒᵖᵐᵒᵖ) : .mk a.get = a := rfl
@[simp] public theorem get_mk (a: α) : get (.mk a) = a := rfl

@[ext] public theorem ext (a b: αᵐᵒᵖ) (h: a.get = b.get) : a = b := h
@[induction_eliminator] public def rec {motive: αᵐᵒᵖ -> Sort u} (mk: ∀a, motive (mk a)) (a: αᵐᵒᵖ) : motive a := mk _

attribute [local irreducible] MulOpp

public instance [One α] : One (αᵐᵒᵖ) where
  one := .mk 1
public instance [Mul α] : Mul (αᵐᵒᵖ) where
  mul a b := .mk (b.get * a.get)
public instance [Pow α β] : Pow (αᵐᵒᵖ) β where
  pow x a := .mk (x.get ^ a)
public instance [Inv α] : Inv (αᵐᵒᵖ) where
  inv a := .mk (a.get⁻¹)
public instance [Mul α] [Inv α] : Div (αᵐᵒᵖ) where
  div a b := a * b⁻¹

@[simp] public theorem get_one [One α] : get 1 = (1: α) := rfl
@[simp] public theorem get_mul [Mul α] (a b: αᵐᵒᵖ) : get (a * b) = b.get * a.get := rfl
@[simp] public theorem get_pow [Pow α β] (a: αᵐᵒᵖ) (b: β) : get (a ^ b) = a.get ^ b := rfl
@[simp] public theorem get_inv [Inv α] (a: αᵐᵒᵖ) : get (a⁻¹) = a.get⁻¹ := rfl

end MulOpp

namespace AddOpp

@[expose] public def mk : α -> αᵃᵒᵖ := id
@[expose] public def get : αᵃᵒᵖ -> α := id

@[simp] public theorem mk_get (a: αᵃᵒᵖᵃᵒᵖ) : .mk a.get = a := rfl
@[simp] public theorem get_mk (a: α) : get (.mk a) = a := rfl

@[ext] public theorem ext (a b: αᵃᵒᵖ) (h: a.get = b.get) : a = b := h
@[induction_eliminator] public def rec {motive: αᵃᵒᵖ -> Sort u} (mk: ∀a, motive (mk a)) (a: αᵃᵒᵖ) : motive a := mk _

attribute [local irreducible] AddOpp

public instance [Zero α] : Zero (αᵃᵒᵖ) where
  zero := .mk 0
public instance [Add α] : Add (αᵃᵒᵖ) where
  add a b := .mk (b.get + a.get)
public instance [SMul β α] : SMul β (αᵃᵒᵖ) where
  smul a x := .mk (a • x.get)
public instance [Neg α] : Neg (αᵃᵒᵖ) where
  neg a := .mk (-a.get)
public instance [Add α] [Neg α] : Sub (αᵃᵒᵖ) where
  sub a b := a + -b

@[simp] public theorem get_zero [Zero α] : get 0 = (0: α) := rfl
@[simp] public theorem get_add [Add α] (a b: αᵃᵒᵖ) : get (a + b) = b.get + a.get := rfl
@[simp] public theorem get_smul [SMul β α] (a: αᵃᵒᵖ) (b: β) : get (b • a) = b • a.get := rfl
@[simp] public theorem get_neg [Neg α] (a: αᵃᵒᵖ) : get (-a) = -a.get := rfl

end AddOpp

@[expose] public def lsmul [SMul R A] (r: R) (a: A) := r • a
@[expose] public def rsmul [SMul Rᵐᵒᵖ A] (a: A) (r: R) := MulOpp.mk r • a

infixr:73 " •> " => lsmul
infixl:73 " <• " => rsmul
