import LeanMath.Logic.Funlike
import LeanMath.Data.AddMul

class IsSemigroup (α: Type*) [Mul α] : Prop where
  protected mul_assoc (a b c: α) : (a * b) * c = a * (b * c)

class IsAddSemigroup (α: Type*) [Add α] where
  protected add_assoc (a b c: α) : (a + b) + c = a + (b + c)

def mul_assoc [Mul α] [IsSemigroup α] (a b c: α) : (a * b) * c = a * (b * c) :=
  IsSemigroup.mul_assoc a b c
def add_assoc [Add α] [IsAddSemigroup α] (a b c: α) : (a + b) + c = a + (b + c) :=
  IsAddSemigroup.add_assoc a b c

class IsCommAt {α: Type*} [Mul α] (a b: α) where
  protected mul_comm : a * b = b * a
class IsAddCommAt {α: Type*} [Add α] (a b: α) where
  protected add_comm : a + b = b + a

class IsComm (α: Type*) [Mul α] where
  protected mul_comm (a b: α) : a * b = b * a
class IsAddComm (α: Type*) [Add α] where
  protected add_comm (a b: α) : a + b = b + a

instance (priority := 1000000) [Mul α] [IsComm α] (a b: α) : IsCommAt a b where
  mul_comm := IsComm.mul_comm a b

instance (priority := 1000000) [Add α] [IsAddComm α] (a b: α) : IsAddCommAt a b where
  add_comm := IsAddComm.add_comm a b

def mul_comm [Mul α] (a b: α) [IsCommAt a b] : a * b = b * a := IsCommAt.mul_comm
def add_comm [Add α] (a b: α) [IsAddCommAt a b] : a + b = b + a := IsAddCommAt.add_comm

class IsMulHom (F α β: Type*) [FunLike F α β] [Mul α] [Mul β] where
  protected map_mul (f: F) (a₀ a₁: α) : f (a₀ * a₁) = f a₀ * f a₁ := by intro f; exact f.map_mul
class IsAddHom (F α β: Type*) [FunLike F α β] [Add α] [Add β] where
  protected map_add (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ + f a₁ := by intro f; exact f.map_add
class IsLogHom (F α β: Type*) [FunLike F α β] [Mul α] [Add β] where
  protected map_mul_to_add (f: F) (a₀ a₁: α) : f (a₀ * a₁) = f a₀ + f a₁ := by intro f; exact f.map_mul_to_add
class IsExpHom (F α β: Type*) [FunLike F α β] [Add α] [Mul β] where
  protected map_add_to_mul (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ * f a₁  := by intro f; exact f.map_add_to_mul

structure Hom (α β: Type*) where
  toFun : α → β

structure MulHom (α β: Type*) [Mul α] [Mul β] extends Hom α β where
  protected map_mul (a₀ a₁): toFun (a₀ * a₁) = toFun a₀ * toFun a₁

structure AddHom (α β: Type*) [Add α] [Add β] extends Hom α β where
  protected map_add (a₀ a₁): toFun (a₀ + a₁) = toFun a₀ + toFun a₁

structure LogHom (α β: Type*) [Mul α] [Add β] extends Hom α β where
  protected map_mul_to_add (a₀ a₁): toFun (a₀ * a₁) = toFun a₀ + toFun a₁

structure ExpHom (α β: Type*) [Add α] [Mul β] extends Hom α β where
  protected map_add_to_mul (a₀ a₁): toFun (a₀ + a₁) = toFun a₀ * toFun a₁

infixr:80 " →*ₙ " => MulHom
infixr:80 " →+ₙ " => AddHom
infixr:80 " →*+ₙ " => LogHom
infixr:80 " →+*ₙ " => ExpHom

section

variable
  [FunLike F α β] [Add α] [Add β] [Mul α] [Mul β]
  [IsMulHom F α β] [IsAddHom F α β] [IsLogHom F α β] [IsExpHom F α β]

def map_mul (f: F) (a₀ a₁: α) : f (a₀ * a₁) =f a₀ * f a₁ := IsMulHom.map_mul f a₀ a₁

def map_add (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ + f a₁ := IsAddHom.map_add f a₀ a₁

def map_add_to_mul (f: F) (a₀ a₁: α) : f (a₀ * a₁) = f a₀ + f a₁ := IsLogHom.map_mul_to_add f a₀ a₁

def map_mul_to_add (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ * f a₁ := IsExpHom.map_add_to_mul f a₀ a₁

instance (priority := 10000) : FunLike (Hom α β) α β where
instance (priority := 10000) : FunLike (α →*ₙ β) α β where
instance (priority := 10000) : FunLike (α →+ₙ β) α β where
instance (priority := 10000) : FunLike (α →+*ₙ β) α β where
instance (priority := 10000) : FunLike (α →*+ₙ β) α β where

instance (priority := 10000) : IsMulHom (α →*ₙ β) α β where
instance (priority := 10000) : IsAddHom (α →+ₙ β) α β where
instance (priority := 10000) : IsLogHom (α →*+ₙ β) α β where
instance (priority := 10000) : IsExpHom (α →+*ₙ β) α β where

attribute [local irreducible] AddOfMul MulOfAdd

def AddOfMul.mkHomₙ : α →*+ₙ AddOfMul α where
  toFun := AddOfMul.mk
  map_mul_to_add _ _ := rfl

def AddOfMul.getHomₙ : AddOfMul α →+*ₙ α where
  toFun := AddOfMul.get
  map_add_to_mul _ _ := rfl

def MulOfAdd.mkHomₙ : α →+*ₙ MulOfAdd α where
  toFun := MulOfAdd.mk
  map_add_to_mul _ _ := rfl

def MulOfAdd.getHomₙ : MulOfAdd α →*+ₙ α where
  toFun := MulOfAdd.get
  map_mul_to_add _ _ := rfl

end

instance : IsSemigroup Nat where
  mul_assoc := Nat.mul_assoc
instance : IsSemigroup Int where
  mul_assoc := Int.mul_assoc
instance : IsAddSemigroup Nat where
  add_assoc := Nat.add_assoc
instance : IsAddSemigroup Int where
  add_assoc := Int.add_assoc

instance : IsComm Nat where
  mul_comm := Nat.mul_comm
instance : IsComm Int where
  mul_comm := Int.mul_comm
instance : IsAddComm Nat where
  add_comm := Nat.add_comm
instance : IsAddComm Int where
  add_comm := Int.add_comm

instance [Mul α] [IsSemigroup α] : Std.Associative (α := α) (· * ·) where
  assoc := mul_assoc
instance [Add α] [IsAddSemigroup α] : Std.Associative (α := α) (· + ·) where
  assoc := add_assoc
instance [Mul α] [IsComm α] : Std.Commutative (α := α) (· * ·) where
  comm _ _ := mul_comm _ _
instance [Add α] [IsAddComm α] : Std.Commutative (α := α) (· + ·) where
  comm _ _ := add_comm _ _
