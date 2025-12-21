import LeanMath.Tactic.TypeStar

def AddOfMul (α: Type*) := α
def MulOfAdd (α: Type*) := α

def AddOfMul.mk : α -> AddOfMul α := id
def AddOfMul.get : AddOfMul α -> α := id

def MulOfAdd.mk : α -> MulOfAdd α := id
def MulOfAdd.get : MulOfAdd α -> α := id

attribute [local irreducible] AddOfMul MulOfAdd

def AddOfMul.induction {motive: AddOfMul α -> Prop} (mk: ∀a, motive (.mk a)) (a: AddOfMul α) : motive a := mk a.get
def MulOfAdd.induction {motive: MulOfAdd α -> Prop} (mk: ∀a, motive (.mk a)) (a: MulOfAdd α) : motive a := mk a.get

instance [One α] : Zero (AddOfMul α) where
  zero := .mk 1
instance [Mul α] : Add (AddOfMul α) where
  add a b := .mk (a.get * b.get)
instance [Pow α β] : SMul β (AddOfMul α) where
  smul n a := .mk (a.get ^ n)
instance [Div α] : Sub (AddOfMul α) where
  sub a b := .mk (a.get / b.get)
instance [Inv α] : Neg (AddOfMul α) where
  neg a := .mk (a.get⁻¹)

instance [Zero α] : One (MulOfAdd α) where
  one := .mk 0
instance [Add α] : Mul (MulOfAdd α) where
  mul a b := .mk (a.get + b.get)
instance [SMul β α] : Pow (MulOfAdd α) β where
  pow a n := .mk (n • a.get)
instance [Sub α] : Div (MulOfAdd α) where
  div a b := .mk (a.get - b.get)
instance [Neg α] : Inv (MulOfAdd α) where
  inv a := .mk (-a.get)
