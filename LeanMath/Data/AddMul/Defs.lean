import LeanMath.Tactic.TypeStar
import LeanMath.Data.Equiv.Defs

def AddOfMul (α: Type*) := α
def MulOfAdd (α: Type*) := α
def MulOpp (α: Type*) := α
def AddOpp (α: Type*) := α

def AddOfMul.mk : α -> AddOfMul α := id
def AddOfMul.get : AddOfMul α -> α := id

def MulOfAdd.mk : α -> MulOfAdd α := id
def MulOfAdd.get : MulOfAdd α -> α := id

def MulOpp.mk : α -> MulOpp α := id
def MulOpp.get : MulOpp α -> α := id
@[simp] def MulOpp.mk_get (x: α) : (MulOpp.mk x).get = x := rfl

def AddOpp.mk : α -> AddOpp α := id
def AddOpp.get : AddOpp α -> α := id

postfix:max "ᵃᵒᵖ" => AddOpp
postfix:max "ᵐᵒᵖ" => MulOpp

def lsmul [SMul R A] (r: R) (a: A) := r • a
def rsmul [SMul Rᵐᵒᵖ A] (a: A) (r: R) := MulOpp.mk r • a

infixr:73 " •> " => lsmul
infixl:73 " <• " => rsmul

def lsmul_eq_smul [SMul R A] (r: R) (a: A) : r •> a = r • a := rfl
def rsmul_eq_smul [SMul Rᵐᵒᵖ A] (r: R) (a: A) : a <• r = MulOpp.mk r • a := rfl

attribute [local irreducible] AddOfMul MulOfAdd MulOpp AddOpp

def AddOfMul.equiv : α ≃ AddOfMul α where
  toFun := mk
  invFun := get
  leftInv _ := rfl
  rightInv _ := rfl

def MulOfAdd.equiv : α ≃ MulOfAdd α where
  toFun := mk
  invFun := get
  leftInv _ := rfl
  rightInv _ := rfl

def MulOpp.equiv : α ≃ MulOpp α where
  toFun := mk
  invFun := get
  leftInv _ := rfl
  rightInv _ := rfl

def AddOpp.equiv : α ≃ AddOpp α where
  toFun := mk
  invFun := get
  leftInv _ := rfl
  rightInv _ := rfl

def AddOfMul.induction {motive: AddOfMul α -> Prop} (mk: ∀a, motive (.mk a)) (a: AddOfMul α) : motive a := mk a.get
def MulOfAdd.induction {motive: MulOfAdd α -> Prop} (mk: ∀a, motive (.mk a)) (a: MulOfAdd α) : motive a := mk a.get
def MulOpp.induction {motive: MulOpp α -> Prop} (mk: ∀a, motive (.mk a)) (a: MulOpp α) : motive a := mk a.get
def AddOpp.induction {motive: AddOpp α -> Prop} (mk: ∀a, motive (.mk a)) (a: AddOpp α) : motive a := mk a.get

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

instance [One α] : One (MulOpp α) where
  one := .mk 1
instance [Mul α] : Mul (MulOpp α) where
  mul a b := .mk (b.get * a.get)
instance [Pow α ℕ] : Pow (MulOpp α) ℕ where
  pow a n := .mk (a.get ^ n)

instance [Inv α] : Inv (MulOpp α) where
  inv a := .mk (a.get⁻¹)

@[simp] def MulOpp.mul_get [Mul α] (a b: MulOpp α) : (a * b).get = b.get * a.get := rfl
