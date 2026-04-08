import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.Module.Defs

section

variable [Zero α] [One α] [Add α] [Mul α] [SMul R α] [Zero β] [One β] [Add β] [Mul β] [SMul R β]

structure NonUnitalAlgebraHom (R α β: Type*)
  [Add α] [Mul α] [SMul R α] [Add β] [Mul β] [SMul R β]
  extends α →ₗ[R] β, MulHom α β where

instance : FunLike (NonUnitalAlgebraHom R α β) α β where
instance : IsAddHom (NonUnitalAlgebraHom R α β) α β where
instance : IsMulHom (NonUnitalAlgebraHom R α β) α β where
instance : IsSMulHom (NonUnitalAlgebraHom R α β) R α β where

instance [Zero R] [IsLawfulZeroSMul R α] [IsLawfulZeroSMul R β] : IsZeroHom (NonUnitalAlgebraHom R α β) α β where
  map_zero := by
    intro f
    rw [←zero_smul (R := R) (0: α), map_smul, zero_smul]

notation:25 A " →ₐ₀[" R "] " B => NonUnitalAlgebraHom R A B

structure AlgebraHom (R α β: Type*) [SMul R α] [SMul R β]
  [Zero α] [One α] [Add α] [Mul α]
  [Zero β] [One β] [Add β] [Mul β]
  extends α →+* β, SMulHom R α β where

structure AlgebraEquiv (R α β: Type*) [SMul R α] [SMul R β]
  [Zero α] [One α] [Add α] [Mul α]
  [Zero β] [One β] [Add β] [Mul β]
  extends α ≃+* β, SMulEquiv R α β where

notation:25 A " →ₐ[" R "] " B => AlgebraHom R A B
notation:25 A " ≃ₐ[" R "] " B => AlgebraEquiv R A B

instance : FunLike (α →ₐ[R] β) α β where
instance : IsZeroHom (α →ₐ[R] β) α β where
instance : IsOneHom (α →ₐ[R] β) α β where
instance : IsAddHom (α →ₐ[R] β) α β where
instance : IsMulHom (α →ₐ[R] β) α β where
instance : IsSMulHom (α →ₐ[R] β) R α β where

instance : EquivLike (α ≃ₐ[R] β) α β where
instance : IsZeroHom (α ≃ₐ[R] β) α β where
instance : IsOneHom (α ≃ₐ[R] β) α β where
instance : IsAddHom (α ≃ₐ[R] β) α β where
instance : IsMulHom (α ≃ₐ[R] β) α β where
instance : IsSMulHom (α ≃ₐ[R] β) R α β where

end

class AlgebraMap (R α: Type*) [SemiringOps R] [SemiringOps α] where
  protected toAlgebraMap : R →+* α

def algebraMap (R: Type*) [SemiringOps R] [SemiringOps α] [AlgebraMap R α] : R →+* α :=
  AlgebraMap.toAlgebraMap

class IsNonUnitalAlgebra (R α: Type*)
  [AddMonoidOps R] [Mul R]
  [AddMonoidOps α] [Mul α]
  [SMul R α]
  [IsNonUnitalNonAssocSemiring R] [IsNonUnitalNonAssocSemiring α] : Prop
  extends IsLawfulSMulZero R α where
  protected smul_compat (r s: R) (a b: α) : (r • a) * (s • b) = (r * s) • (a * b)

section

variable
  [AddMonoidOps R] [Mul R]
  [AddMonoidOps α] [AddMonoidOps β] [AddMonoidOps γ]
  [Mul α] [Mul β] [Mul γ] [SMul R α] [SMul R β] [SMul R γ]
  [IsNonUnitalNonAssocSemiring R]
  [IsNonUnitalNonAssocSemiring α] [IsNonUnitalNonAssocSemiring β]
  [IsNonUnitalNonAssocSemiring γ]

def smul_compat [IsNonUnitalAlgebra R α] (r s: R) (a b: α) : (r • a) * (s • b) = (r * s) • (a * b) :=
  IsNonUnitalAlgebra.smul_compat _ _ _ _

end

class IsAlgebra (R α: Type*)
  [SemiringOps R] [SemiringOps α]
  [SMul R α] [AlgebraMap R α]
  [IsSemiring R] [IsSemiring α] : Prop where
  protected commutes (r: R) (a: α) : algebraMap R r * a = a * algebraMap R r
  protected smul_def (r: R) (a: α) : r • a = algebraMap R r * a

variable
  [SemiringOps R] [SemiringOps α] [SemiringOps β] [SemiringOps γ]
  [SMul R α] [AlgebraMap R α]
  [SMul R β] [AlgebraMap R β]
  [SMul R γ] [AlgebraMap R γ]
  [IsSemiring R] [IsSemiring α] [IsSemiring β] [IsSemiring γ]

def commutes [IsAlgebra R α] (r: R) (a: α) : algebraMap R r * a = a * algebraMap R r :=
  IsAlgebra.commutes _ _

def smul_def [IsAlgebra R α] (r: R) (a: α) : r • a = algebraMap R r * a :=
  IsAlgebra.smul_def _ _

instance [IsAlgebra R α] (r :R) (a: α) : IsCommAt (algebraMap R r) a where
  mul_comm := IsAlgebra.commutes _ _
instance [IsAlgebra R α] (r :R) (a: α) : IsCommAt a (algebraMap R r) := inferInstance

instance (priority := 900) : AlgebraMap R R where
  toAlgebraMap := {
    toFun := id
    map_one := rfl
    map_zero := rfl
    map_add _ _ := rfl
    map_mul _ _ := rfl
  }

def algebraMap_id (x: R) : algebraMap R x = x := rfl

instance [IsComm R] : IsAlgebra R R where
  commutes _ _ := mul_comm _ _
  smul_def _ _ := rfl

instance (priority := 500) [SemiringOps R] [IsSemiring R] : AlgebraMap Nat R where
  toAlgebraMap := natCastHom

instance [SemiringOps R] [IsSemiring R] : IsAlgebra Nat R where
  commutes r x := by
    show r * x = x * r
    rw [←nsmul_eq_natCast_mul, ←nsmul_eq_mul_natCast]
  smul_def a b := by rw [nsmul_eq_natCast_mul]; rfl

def map_algebraMap [IsAlgebra R α] [IsAlgebra R β] (f: F) [FunLike F α β] [IsSMulHom F R α β] [IsMulHom F α β] [IsOneHom F α β] : f (algebraMap R r) = algebraMap R r := by
  rw [←mul_one (algebraMap R r), ←mul_one (algebraMap (α := β) R r)]
  rw [←smul_def, ←smul_def, map_smul, map_one]

@[ext]
def AlgebraHom.ext (f g: α →ₐ[R] β) : (∀x, f x = g x) -> f = g := DFunLike.ext _ _

@[simp] def SMulEquiv.apply_toEquiv (f: SMulEquiv R α β) : f.toEquiv x = f x := rfl
def SMulEquiv.comp (f: SMulEquiv R β γ) (g: SMulEquiv R α β) : SMulEquiv R α γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_smul := by
    intro r a
    dsimp
    rw [map_smul, map_smul]

def SMulEquiv.symm (f: SMulEquiv R α β) : SMulEquiv R β α where
  toEquiv := f.toEquiv.symm
  map_smul a b := by
    apply f.inj; dsimp
    rw (occs := [2]) [map_smul]
    apply Eq.trans; apply Equiv.symm_coe
    congr <;> (symm; apply Equiv.symm_coe)

def AlgebraEquiv.comp (f: β ≃ₐ[R] γ) (g: α ≃ₐ[R] β) : α ≃ₐ[R] γ where
  toRingEquiv := f.toRingEquiv.comp g.toRingEquiv
  map_smul := map_smul (f.toSMulEquiv.comp g.toSMulEquiv)
def AlgebraEquiv.trans (g: α ≃ₐ[R] β) (f: β ≃ₐ[R] γ) : α ≃ₐ[R] γ := f.comp g

def AlgebraEquiv.apply_comp (f: β ≃ₐ[R] γ) (g: α ≃ₐ[R] β) : (f.comp g) x = f (g x) := rfl
def AlgebraEquiv.apply_trans (g: α ≃ₐ[R] β) (f: β ≃ₐ[R] γ) : (g.trans f) x = f (g x) := rfl

def AlgebraEquiv.symm (f: α ≃ₐ[R] β) : β ≃ₐ[R] α where
  toRingEquiv := f.toRingEquiv.symm
  map_smul := map_smul f.toSMulEquiv.symm

@[simp] def AlgebraEquiv.coe_symm (f: α ≃ₐ[R] β) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def AlgebraEquiv.symm_coe (f: α ≃ₐ[R] β) : f (f.symm x) = x := Equiv.symm_coe _ _

def AlgebraEquiv.refl (R α: Type*) [SMul R α] [SemiringOps α] : α ≃ₐ[R] α where
  toRingEquiv := .refl α
  map_smul _ _ := rfl

@[simp] def AlgebraEquiv.apply_refl (x: α) : AlgebraEquiv.refl R _ x = x := rfl

private class AlgebraEquiv.Ops (R α: Type u) extends
  SMul R α, SemiringOps α where
instance : EquivOpsCheck (AlgebraEquiv.Ops R) (fun α β _ _ => α ≃ₐ[R] β) where
  comp := .comp
  trans := .trans
  symm := .symm
  refl _ := .refl R _

-- every algebra is also a module
instance [IsAlgebra R α] : IsModule R α where
  one_smul a := by rw [smul_def, map_one, one_mul]
  mul_smul r s a := by rw [smul_def, smul_def, smul_def, map_mul, mul_assoc]
  smul_zero r := by rw [smul_def, mul_zero]
  smul_add r a b := by rw [smul_def, smul_def, smul_def, mul_add]
  zero_smul a := by rw [smul_def, map_zero, zero_mul]
  add_smul r s a := by rw [smul_def, smul_def, smul_def, map_add, add_mul]

instance [IsAlgebra R α] : IsNonUnitalAlgebra R α where
  smul_compat r s a b := by
    rw [smul_def, smul_def, smul_def,
      map_mul, mul_assoc, mul_left_comm a, ←mul_assoc]

instance : AlgebraMap ℕ α where
  toAlgebraMap := natCastHom
instance : IsAlgebra ℕ α where
  smul_def n a := by rw [nsmul_eq_natCast_mul]; rfl
  commutes n a := by
    show n * a = a * n
    rw [mul_comm]

namespace IsAlgebra

-- an `α`-algebra structure on `β` given by the ring homomorphism
def OfRingHom (f: α →+* β) (_: ∀a b, f a * b = b * f a) := β

variable {f: α →+* β} {h: ∀a b, f a * b = b * f a}
def OfRingHom.get : OfRingHom f h -> β := id
def OfRingHom.mk : β -> OfRingHom f h := id

instance : SemiringOps (OfRingHom f h) := inferInstanceAs (SemiringOps β)
instance : IsSemiring (OfRingHom f h) := inferInstanceAs (IsSemiring β)
instance [IsComm β] : IsComm (OfRingHom f h) := inferInstanceAs (IsComm β)
instance : AlgebraMap α (OfRingHom f h) where
  toAlgebraMap := f
instance : SMul α (OfRingHom f h) where
  smul a b := algebraMap α a * b
instance : IsAlgebra α (OfRingHom f h) where
  smul_def _ _ := rfl
  commutes := h

end IsAlgebra

namespace OfEquiv

variable {R α: Type*} (f: α ≃ β)

protected scoped instance algebraMap [SemiringOps R] [SemiringOps β] [AlgebraMap R β] : AlgebraMap R (OfEquiv f) where
  toAlgebraMap := (ringEquiv f).symm.toRingHom.comp (algebraMap R)

@[simp] def apply_algebraMap [SemiringOps R] [SemiringOps β] [AlgebraMap R β]
  (r: R) : algebraMap (α := OfEquiv f) R r = f.symm (algebraMap R r) := rfl

protected scoped instance
  [AddMonoidOps R] [Mul R]
  [AddMonoidOps β] [Mul β]
  [SMul R β]
  [IsNonUnitalNonAssocSemiring R] [IsNonUnitalNonAssocSemiring β]
  [IsNonUnitalAlgebra R β]
: IsNonUnitalAlgebra R (OfEquiv f) where
  smul_compat (r s: R) (a b: α) := by dsimp; rw [Equiv.symm_coe, Equiv.symm_coe, Equiv.symm_coe, smul_compat]

protected scoped instance
  [SemiringOps R] [SemiringOps β]
  [SMul R β] [AlgebraMap R β]
  [IsSemiring R] [IsSemiring β]
  [IsAlgebra R β] :
  IsAlgebra R (OfEquiv f) where
  commutes (r: R) (a: α) := by dsimp; rw [Equiv.symm_coe, commutes]
  smul_def (r: R) (a: α) := by dsimp; rw [Equiv.symm_coe, _root_.smul_def]

end OfEquiv
