import LeanMath.Data.Equiv.Defs

def OfEquiv (_: α ≃ β) := α

namespace OfEquiv

variable (f: α ≃ β)

protected scoped instance mul [Mul β] : Mul (OfEquiv f) where
  mul a b := f.symm (f a * f b)
protected scoped instance add [Add β] : Add (OfEquiv f) where
  add a b := f.symm (f a + f b)

protected scoped instance smul (R: Type*) [SMul R β] : SMul R (OfEquiv f) where
  smul r a := f.symm (r • f a)
protected scoped instance pow (R: Type*) [Pow β R] : Pow (OfEquiv f) R where
  pow a r := f.symm (f a ^ r)

protected scoped instance inv [Inv β] : Inv (OfEquiv f) where
  inv a := f.symm (f a)⁻¹
protected scoped instance neg [Neg β] : Neg (OfEquiv f) where
  neg a := f.symm (-f a)

protected scoped instance div [Div β] : Div (OfEquiv f) where
  div a b := f.symm (f a / f b)
protected scoped instance sub [Sub β] : Sub (OfEquiv f) where
  sub a b := f.symm (f a - f b)

protected scoped instance one [One β] : One (OfEquiv f) where
  one := f.symm 1
protected scoped instance zero [Zero β] : Zero (OfEquiv f) where
  zero := f.symm 0

protected scoped instance natCast [NatCast β] : NatCast (OfEquiv f) where
  natCast n := f.symm n
protected scoped instance intCast [IntCast β] : IntCast (OfEquiv f) where
  intCast n := f.symm n

protected scoped instance [LT β] : LT (OfEquiv f) where
  lt a b := f a < f b
protected scoped instance [LE β] : LE (OfEquiv f) where
  le a b := f a ≤ f b

protected scoped instance [Min β] : Min (OfEquiv f) where
  min a b := f.symm <| min (f a) (f b)
protected scoped instance [Max β] : Max (OfEquiv f) where
  max a b := f.symm <| max (f a) (f b)

@[simp] def mul_def [Mul β] (a b: OfEquiv f) : a * b = f.symm (f a * f b) := rfl
@[simp] def add_def [Add β] (a b: OfEquiv f) : a + b = f.symm (f a + f b) := rfl

@[simp] def inv_def [Inv β] (a: OfEquiv f) : a⁻¹ = f.symm (f a)⁻¹ := rfl
@[simp] def neg_def [Neg β] (a: OfEquiv f) : -a = f.symm (-f a) := rfl

@[simp] def div_def [Div β] (a b: OfEquiv f) : a / b = f.symm (f a / f b) := rfl
@[simp] def sub_def [Sub β] (a b: OfEquiv f) : a - b = f.symm (f a - f b) := rfl

@[simp] def smul_def [SMul R β] (r: R) (a: OfEquiv f) : r • a = f.symm (r • f a) := rfl
@[simp] def pow_def [Pow β R] (a: OfEquiv f) (r: R) : a ^ r = f.symm (f a ^ r) := rfl

@[simp] def one_def [One β] : (1: OfEquiv f) = f.symm 1 := rfl
@[simp] def zero_def [Zero β] : (0: OfEquiv f) = f.symm 0 := rfl

@[simp] def natCast_def [NatCast β] (n: ℕ) : (n: OfEquiv f) = f.symm n := rfl
@[simp] def intCast_def [IntCast β] (n: ℤ) : (n: OfEquiv f) = f.symm n := rfl

@[simp] def lt_def [LT β] (a b: OfEquiv f) : (a < b) = (f a < f b) := rfl
@[simp] def le_def [LE β] (a b: OfEquiv f) : (a ≤ b) = (f a ≤ f b) := rfl

@[simp] def min_def [Min β] (a b: OfEquiv f) : min a b = f.symm (min (f a) (f b)) := rfl
@[simp] def max_def [Max β] (a b: OfEquiv f) : max a b = f.symm (max (f a) (f b)) := rfl

end OfEquiv
