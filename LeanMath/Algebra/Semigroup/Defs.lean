import LeanMath.Logic.Funlike

class IsSemigroup (α: Type*) [Mul α] : Prop where
  protected mul_assoc (a b c: α) : a * (b * c) = (a * b) * c

class IsAddSemigroup (α: Type*) [Add α] where
  protected add_assoc (a b c: α) : a + (b + c) = (a + b) + c

def mul_assoc [Mul α] [IsSemigroup α] (a b c: α) : a * (b * c) = (a * b) * c :=
  IsSemigroup.mul_assoc a b c
def add_assoc [Add α] [IsAddSemigroup α] (a b c: α) : a + (b + c) = (a + b) + c :=
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
  protected map_mul (f: F) (a₀ a₁: α) : f a₀ * f a₁ = f (a₀ * a₁)
class IsAddHom (F α β: Type*) [FunLike F α β] [Add α] [Add β] where
  protected map_add (f: F) (a₀ a₁: α) : f a₀ + f a₁ = f (a₀ + a₁)
