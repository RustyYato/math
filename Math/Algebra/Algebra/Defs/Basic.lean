module

public import Math.Algebra.Module.Defs.Basic
public import Math.Algebra.Module.Hom.Defs

namespace Math

section Property

public class AlgebraMap (R α: Type*) [SemiringOps R] [SemiringOps α] extends R →+* α where

@[expose] public def algebraMap (R: Type*) {α: Type*} [SemiringOps R] [SemiringOps α] [AlgebraMap R α] : R →+* α :=
  AlgebraMap.toRingHom

public class IsAlgebra (R α: Type*) [SemiringOps R] [SemiringOps α] [IsSemiring R] [IsSemiring α] [AlgebraMap R α] [SMul R α] where
  commutes (r: R) (a: α) : algebraMap R r * a = a * algebraMap R r
  smul_def (r: R) (a: α) : r • a = algebraMap R r * a

export IsAlgebra (commutes smul_def)

variable [SemiringOps R] [SemiringOps α] [AlgebraMap R α] [SMul R α]

public instance [IsSemiring R] [IsSemiring α] [IsAlgebra R α] (r: R) (a: α) : IsCommAt (algebraMap R r) a where
  mul_comm := by rw [commutes]
public instance [IsSemiring R] [IsSemiring α] [IsAlgebra R α] (r: R) (a: α) : IsCommAt a (algebraMap R r) := inferInstance

public instance (priority := 900) : AlgebraMap R R where
  toRingHom := {
    toFun := id
    map_one := rfl
    map_zero := rfl
    map_add _ _ := rfl
    map_mul _ _ := rfl
  }

@[simp] public theorem apply_algebraMap_id (r: R) : algebraMap R r = r := rfl

public instance [IsSemiring α] [IsComm α] : IsAlgebra α α where
  commutes _ _ := mul_comm _ _
  smul_def _ _ := rfl

public instance [IsSemiring R] : AlgebraMap ℕ R where
  toRingHom := RingHom.natCast

public instance [IsSemiring R] : IsAlgebra ℕ R where
  commutes r x := by
    show r * x = x * r
    rw [←nsmul_eq_natCast_mul, ←nsmul_eq_mul_natCast]
  smul_def a b := by rw [nsmul_eq_natCast_mul]; rfl

public instance [IsSemiring R] [IsSemiring α] [IsAlgebra R α] : IsModule R α where
  one_smul a := by rw [smul_def, map_one, one_mul]
  mul_smul r s a := by rw [smul_def, smul_def, smul_def, map_mul, mul_assoc]
  smul_zero r := by rw [smul_def, mul_zero]
  smul_add r a b := by rw [smul_def, smul_def, smul_def, mul_add]
  zero_smul a := by rw [smul_def, map_zero, zero_mul]
  add_smul r s a := by rw [smul_def, smul_def, smul_def, map_add, add_mul]

end Property

section Hom

section Defs

public structure AlgebraHom (R α β: Type*)
  [Add α] [Mul α] [Zero α] [One α] [SMul R α]
  [Add β] [Mul β] [Zero β] [One β] [SMul R β] extends α →+* β, SMulHom R α β where

public structure AlgebraEmbedding (R α β: Type*)
  [Add α] [Mul α] [Zero α] [One α] [SMul R α]
  [Add β] [Mul β] [Zero β] [One β] [SMul R β] extends α ↪+* β, AlgebraHom R α β where

public structure AlgebraEquiv (R α β: Type*)
  [Add α] [Mul α] [Zero α] [One α] [SMul R α]
  [Add β] [Mul β] [Zero β] [One β] [SMul R β] extends α ≃+* β, SMulEquiv R α β, AlgebraHom R α β where

notation:25 A " →ₐ[" R "] " B => AlgebraHom R A B
notation:25 A " ↪ₐ[" R "] " B => AlgebraEmbedding R A B
notation:25 A " ≃ₐ[" R "] " B => AlgebraEquiv R A B

end Defs

section Impls

variable {R α β: Type*} [Add α] [Add β] [Mul α] [Mul β] [Zero α] [Zero β] [One α] [One β] [SMul R α] [SMul R β]

public instance : Funlike (α →ₐ[R] β) α β where
public instance : EmbeddingLike (α ↪ₐ[R] β) α β where
public instance : EquivLike (α ≃ₐ[R] β) α β where

public instance : IsZeroHom (α →ₐ[R] β) α β where
public instance : IsZeroHom (α ↪ₐ[R] β) α β where
public instance : IsZeroHom (α ≃ₐ[R] β) α β where

public instance : IsOneHom (α →ₐ[R] β) α β where
public instance : IsOneHom (α ↪ₐ[R] β) α β where
public instance : IsOneHom (α ≃ₐ[R] β) α β where

public instance : IsAddHom (α →ₐ[R] β) α β where
public instance : IsAddHom (α ↪ₐ[R] β) α β where
public instance : IsAddHom (α ≃ₐ[R] β) α β where

public instance : IsMulHom (α →ₐ[R] β) α β where
public instance : IsMulHom (α ↪ₐ[R] β) α β where
public instance : IsMulHom (α ≃ₐ[R] β) α β where

public instance : IsSMulHom (α →ₐ[R] β) R α β where
public instance : IsSMulHom (α ↪ₐ[R] β) R α β where
public instance : IsSMulHom (α ≃ₐ[R] β) R α β where

end Impls

section Basic

public theorem map_algebraMap
  [SemiringOps R] [IsSemiring R]
  [SemiringOps α] [IsSemiring α]
  [SemiringOps β] [IsSemiring β]
  [SMul R α] [AlgebraMap R α] [IsAlgebra R α]
  [SMul R β] [AlgebraMap R β] [IsAlgebra R β]
  [Funlike F α β] [IsSMulHom F R α β] [IsOneHom F α β]
  (f: F) : f (algebraMap R r) = algebraMap R r := by
  rw [←mul_one (algebraMap R r), ←smul_def, map_smul, map_one, smul_def, mul_one]

end Basic

variable {α β γ: Type*} [Add α] [Mul α] [Zero α] [One α] [SMul R α] [Add β] [Mul β] [Zero β] [One β] [SMul R β] [Add γ] [Mul γ] [Zero γ] [One γ] [SMul R γ]

section Reduction

@[simp] public theorem AlgebraEmbedding.apply_toEmbedding (f: α ↪ₐ[R] β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem AlgebraEquiv.apply_toEquiv (f: α ≃ₐ[R] β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem AlgebraEmbedding.apply_toAlgebraHom (f: α ↪ₐ[R] β) (x: α) : f.toAlgebraHom x = f x := rfl
@[simp] public theorem AlgebraEquiv.apply_toAlgebraHom (f: α ≃ₐ[R] β) (x: α) : f.toAlgebraHom x = f x := rfl

@[ext] public theorem AlgebraHom.ext (f g: α →ₐ[R] β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AlgebraEmbedding.ext (f g: α ↪ₐ[R] β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AlgebraEquiv.ext (f g: α ≃ₐ[R] β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def AlgebraHom.id (R α: Type*) [Add α] [Mul α] [Zero α] [One α] [SMul R α] : α →ₐ[R] α := {
  RingHom.id α, SMulHom.id R α with
}
@[expose] public protected def AlgebraEmbedding.id (R α: Type*) [Add α] [Mul α] [Zero α] [One α] [SMul R α] : α ↪ₐ[R] α := {
  Embedding.id _, AlgebraHom.id _ _ with
}
@[expose] public protected def AlgebraEquiv.id (R α: Type*) [Add α] [Mul α] [Zero α] [One α] [SMul R α] : α ≃ₐ[R] α := {
  Equiv.id _, AlgebraHom.id _ _ with
}

@[expose] public def AlgebraHom.comp (f: β →ₐ[R] γ) (g: α →ₐ[R] β) : α →ₐ[R] γ := {
  f.toRingHom.comp g.toRingHom, f.toSMulHom.comp g.toSMulHom with
}
@[expose] public def AlgebraEmbedding.comp (f: β ↪ₐ[R] γ) (g: α ↪ₐ[R] β) : α ↪ₐ[R] γ := {
  f.toEmbedding.comp g.toEmbedding, f.toAlgebraHom.comp g.toAlgebraHom with
}
@[expose] public def AlgebraEquiv.comp (f: β ≃ₐ[R] γ) (g: α ≃ₐ[R] β) : α ≃ₐ[R] γ := {
  f.toEquiv.comp g.toEquiv, f.toAlgebraHom.comp g.toAlgebraHom with
}
@[expose] public def AlgebraEmbedding.trans (f: α ↪ₐ[R] β) (g: β ↪ₐ[R] γ) : α ↪ₐ[R] γ := comp g f
@[expose] public def AlgebraEquiv.trans (f: α ≃ₐ[R] β) (g: β ≃ₐ[R] γ) : α ≃ₐ[R] γ := comp g f
@[expose] public def AlgebraEquiv.symm (f: α ≃ₐ[R] β) : β ≃ₐ[R] α := {
  f.toRingEquiv.symm, f.toSMulEquiv.symm with
}

end Api

namespace AlgebraHom

@[simp] public theorem apply_id : AlgebraHom.id R α x = x := rfl

@[simp] public theorem apply_comp (f: β →ₐ[R] γ) (g: α →ₐ[R] β) (x: α) : f.comp g x = f (g x) := rfl

end AlgebraHom

namespace AlgebraEmbedding

@[simp] public theorem apply_id : AlgebraEmbedding.id R α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪ₐ[R] γ) (g: α ↪ₐ[R] β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪ₐ[R] β) (g: β ↪ₐ[R] γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪ₐ[R] β) : Function.Injective f := f.injective

end AlgebraEmbedding

namespace AlgebraEquiv

@[simp] public theorem apply_id : AlgebraEquiv.id R α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃ₐ[R] β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃ₐ[R] β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃ₐ[R] β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃ₐ[R] γ) (g: α ≃ₐ[R] β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃ₐ[R] β) (g: β ≃ₐ[R] γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃ₐ[R] β) : f.symm.comp f = AlgebraEquiv.id _ _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃ₐ[R] β) : f.comp f.symm = AlgebraEquiv.id _ _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃ₐ[R] β) : f.symm.trans f = AlgebraEquiv.id _ _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃ₐ[R] β) : f.trans f.symm = AlgebraEquiv.id _ _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃ₐ[R] β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃ₐ[R] β) : Function.Surjective f := f.symm.rightInv.surjective

end AlgebraEquiv

end Hom
