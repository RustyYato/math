module

public import Math.Data.Equiv.Defs
public import Math.Tactic.Basic

namespace Math

@[expose] public def OfEquiv (_f: α ≃ β) := β

namespace OfEquiv

variable {f: α ≃ β}

@[expose] public def mk : α ≃ OfEquiv f := f
@[expose] public def get : OfEquiv f -> α := f.symm
@[induction_eliminator] public theorem induction {motive: OfEquiv f -> Prop} (mk: ∀a: α, motive (mk a)) (a: OfEquiv f) : motive a := by
  rw [←f.symm_apply a]
  apply mk
@[simp] public theorem mk_get (a: OfEquiv f) : mk a.get = a := Equiv.symm_apply f a
@[simp] public theorem get_mk (a: α) : (mk (f := f) a).get = a := Equiv.apply_symm f a

public instance [One α] : One (OfEquiv f) where
  one := .mk 1
public instance [Mul α] : Mul (OfEquiv f) where
  mul a b := .mk (a.get * b.get)
public instance [Pow α γ] : Pow (OfEquiv f) γ where
  pow x a := .mk (x.get ^ a)
public instance [Inv α] : Inv (OfEquiv f) where
  inv a := .mk (a.get⁻¹)
public instance [Div α] : Div (OfEquiv f) where
  div a b := .mk (a.get / b.get)
public instance [Zero α] : Zero (OfEquiv f) where
  zero := .mk 0
public instance [Add α] : Add (OfEquiv f) where
  add a b := .mk (a.get + b.get)
public instance [SMul γ α] : SMul γ (OfEquiv f) where
  smul a x := .mk (a • x.get)
public instance [Neg α] : Neg (OfEquiv f) where
  neg a := .mk (-a.get)
public instance [Sub α] : Sub (OfEquiv f) where
  sub a b := .mk (a.get - b.get)
public instance [NatCast α] : NatCast (OfEquiv f) where
  natCast n := .mk n
public instance [IntCast α] : IntCast (OfEquiv f) where
  intCast n := .mk n

@[simp] public theorem mk_mul [Mul α] (a b: α) : mk (f := f) a * mk b = mk (a * b) := by show mk _ = _; simp
@[simp] public theorem mk_add [Add α] (a b: α) : mk (f := f) a + mk b = mk (a + b) := by show mk _ = _; simp
@[simp] public theorem mk_div [Div α] (a b: α) : mk (f := f) a / mk b = mk (a / b) := by show mk _ = _; simp
@[simp] public theorem mk_sub [Sub α] (a b: α) : mk (f := f) a - mk b = mk (a - b) := by show mk _ = _; simp
@[simp] public theorem mk_pow [Pow α γ] (a: α) (b: γ) : mk (f := f) a ^ b = mk (a ^ b) := by show mk _ = _; simp
@[simp] public theorem mk_smul [SMul γ α] (a: α) (b: γ) : b • mk (f := f) a = mk (b • a) := by show mk _ = _; simp
@[simp] public theorem mk_inv [Inv α] (a: α) : (mk (f := f) a)⁻¹ = mk (a⁻¹) := by show mk _ = _; simp
@[simp] public theorem mk_neg [Neg α] (a: α) : -mk (f := f) a = mk (-a) := by show mk _ = _; simp
@[simp] public theorem mk_one [One α] : 1 = mk (f := f) 1 := by show mk _ = _; simp
@[simp] public theorem mk_zero [Zero α] : 0 = mk (f := f) 0 := by show mk _ = _; simp
@[simp] public theorem mk_natCast [NatCast α] (n: ℕ) : n = mk (f := f) n := by show mk _ = _; simp
@[simp] public theorem mk_intCast [IntCast α] (n: ℤ) : n = mk (f := f) n := by show mk _ = _; simp
