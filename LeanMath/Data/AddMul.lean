import LeanMath.Tactic.TypeStar

def MulToAdd (α: Type*) := α

def MulToAdd.mk : α -> MulToAdd α := id
def MulToAdd.get : MulToAdd α -> α := id

instance [One α] : Zero (MulToAdd α) where
  zero := .mk 1
instance [Mul α] : Add (MulToAdd α) where
  add a b := .mk (a.get * b.get)
instance [Pow α β] : SMul β (MulToAdd α) where
  smul n a := .mk (a.get ^ n)
instance [Div α] : Sub (MulToAdd α) where
  sub a b := .mk (a.get / b.get)
instance [Inv α] : Neg (MulToAdd α) where
  neg a := .mk (a.get⁻¹)
