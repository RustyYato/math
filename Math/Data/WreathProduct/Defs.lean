module

public import Math.Data.SemidirectProduct.Group
public import Math.Algebra.Group.Defs.Prod
public import Math.Algebra.Group.Action.Defs.Basic
public import Math.Algebra.Group.Defs.OfEquiv

import Math.Algebra.Group.Defs.Lemmas

namespace Math

open scoped Automorphism

def preWreathHom
  (A Ω H: Type*)
  [GroupOps H] [IsGroup H] [GroupOps A] [IsGroup A]
  [SMul H Ω] [IsLawfulOneSMul H Ω] [IsLawfulMulSMul H Ω] (h: H) : (Ω -> A) ≃* (Ω -> A) where
  toFun f i := f (h⁻¹ • i)
  invFun f i := f (h • i)
  leftInv f := by
    ext i; dsimp
    rw [←mul_smul, mul_inv_cancel, one_smul]
  rightInv f := by
    ext i; dsimp
    rw [←mul_smul, inv_mul_cancel, one_smul]
  map_one := rfl
  map_mul _ _ := rfl

theorem apply_preWreathHom
  [GroupOps H] [IsGroup H] [GroupOps A] [IsGroup A]
  [SMul H Ω] [IsLawfulOneSMul H Ω] [IsLawfulMulSMul H Ω] (h: H) (f: Ω -> A) (i: Ω) :
  preWreathHom A Ω H h f i = f (h⁻¹ • i) := rfl

public def wreathHom
  (A Ω H: Type*)
  [GroupOps H] [IsGroup H] [GroupOps A] [IsGroup A]
  [SMul H Ω] [IsLawfulOneSMul H Ω] [IsLawfulMulSMul H Ω] : H →* ((Ω -> A) ≃* (Ω -> A)) where
  toFun h := preWreathHom A Ω H h
  map_one := by
    ext f i
    rw [apply_preWreathHom, one_inv (α := H), one_smul]
    rfl
  map_mul h₀ h₁ := by
    ext f i
    show _ = preWreathHom _ _ _ h₁ _ _
    rw [apply_preWreathHom, apply_preWreathHom]
    rw [←inv_mul_inv_rev, mul_smul]

@[simp] public theorem apply_wreathHom
  [GroupOps H] [IsGroup H] [GroupOps A] [IsGroup A]
  [SMul H Ω] [IsLawfulOneSMul H Ω] [IsLawfulMulSMul H Ω] (h: H) (f: Ω -> A) (i: Ω) :
  wreathHom A Ω H h f i = f (h⁻¹ • i) := by rfl

@[simp] public theorem apply_wreathHom_symm
  [GroupOps H] [IsGroup H] [GroupOps A] [IsGroup A]
  [SMul H Ω] [IsLawfulOneSMul H Ω] [IsLawfulMulSMul H Ω] (h: H) (f: Ω -> A) (i: Ω) :
  (wreathHom A Ω H h).symm f i = f (h • i) := by rfl

-- https://en.wikipedia.org/wiki/Wreath_product
public structure WreathProduct (A Ω H: Type*)
  [GroupOps H] [IsGroup H] [GroupOps A] [IsGroup A]
  [SMul H Ω] [IsLawfulOneSMul H Ω] [IsLawfulMulSMul H Ω] where
  ofSemidirect :: toSemidirect : SemidirectProduct (Ω -> A) H (wreathHom A Ω H)

namespace WreathProduct

variable
  {A Ω H: Type*}
  [GroupOps H] [IsGroup H] [GroupOps A] [IsGroup A]
  [SMul H Ω] [IsLawfulOneSMul H Ω] [IsLawfulMulSMul H Ω]

public def eqv : SemidirectProduct (Ω -> A) H (wreathHom A Ω H) ≃ WreathProduct A Ω H where
  toFun := ofSemidirect
  invFun := toSemidirect
  leftInv _ := rfl
  rightInv _ := rfl

public instance : GroupOps (WreathProduct A Ω H) where
  one := ⟨1⟩
  mul a b := ⟨a.toSemidirect * b.toSemidirect⟩
  div a b := ⟨a.toSemidirect / b.toSemidirect⟩
  inv a := ⟨a.toSemidirect⁻¹⟩
  toPowN := ⟨fun a n => ⟨a.toSemidirect ^ n⟩⟩
  toPowZ := ⟨fun a n => ⟨a.toSemidirect ^ n⟩⟩

public instance : IsGroup (WreathProduct A Ω H) :=
  OfEquiv.instIsGroup eqv

end WreathProduct
