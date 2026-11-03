module

public import Math.Algebra.Semigroup.Defs
public import Math.Algebra.Monoid.Action.Defs

namespace Math

section Defs

public class IsSMulHom (F K α β: Type*) [Funlike F α β] [SMul K α] [SMul K β] where
  map_smul (f: F) (k: K) (a: α) : f (k • a) = k • f a := by intro f; exact f.map_smul

export IsSMulHom (map_smul)

public structure SMulHom (K α β: Type*) [SMul K α] [SMul K β] extends Hom α β where
  protected map_smul (k: K) (a: α) : toFun (k • a) = k • toFun a

public structure SMulEquiv (K α β: Type*) [SMul K α] [SMul K β] extends α ≃ β, SMulHom K α β where

public structure LinearHom (K α β: Type*)
  [Add α] [SMul K α] [Add β] [SMul K β]
  extends α →+ₙ β, SMulHom K α β where

public structure LinearEmbedding (K α β: Type*)
  [Add α] [SMul K α] [Add β] [SMul K β]
  extends α ↪ β, LinearHom K α β where

public structure LinearEquiv (K α β: Type*)
  [Add α] [SMul K α] [Add β] [SMul K β]
  extends α ≃ β, LinearHom K α β, SMulEquiv K α β, α ≃+ₙ β where

notation:25 A " →ₗ[" R "] " B => LinearHom R A B
notation:25 A " ↪ₗ[" R "] " B => LinearEmbedding R A B
notation:25 A " ≃ₗ[" R "] " B => LinearEquiv R A B

end Defs

section Impls

variable [Add α] [Add β] [SMul R α] [SMul R β]

public instance : Funlike (SMulHom R α β) α β where
public instance : Funlike (α →ₗ[R] β) α β where
public instance : EmbeddingLike (α ↪ₗ[R] β) α β where
public instance : EquivLike (α ≃ₗ[R] β) α β where
public instance : EquivLike (SMulEquiv R α β) α β where

public instance : IsAddHom (α →ₗ[R] β) α β where
public instance : IsAddHom (α ↪ₗ[R] β) α β where
public instance : IsAddHom (α ≃ₗ[R] β) α β where

public instance : IsSMulHom (SMulHom R α β) R α β where
public instance : IsSMulHom (SMulEquiv R α β) R α β where
public instance : IsSMulHom (α →ₗ[R] β) R α β where
public instance : IsSMulHom (α ↪ₗ[R] β) R α β where
public instance : IsSMulHom (α ≃ₗ[R] β) R α β where

variable [Zero R] [Zero α] [Zero β]
  [IsLawfulZeroSMul R α]
  [IsLawfulZeroSMul R β]

public instance : IsZeroHom (SMulHom R α β) α β where
  map_zero f := by rw [←zero_smul (R := R) (0: α), map_smul, zero_smul]
public instance : IsZeroHom (SMulEquiv R α β) α β where
  map_zero f := map_zero f.toSMulHom
public instance : IsZeroHom (α →ₗ[R] β) α β where
  map_zero f := map_zero f.toSMulHom
public instance : IsZeroHom (α ↪ₗ[R] β) α β where
  map_zero f := map_zero f.toSMulHom
public instance : IsZeroHom (α ≃ₗ[R] β) α β where
  map_zero f := map_zero f.toSMulHom

end Impls

section Reduction

@[simp] public theorem SMulEquiv.apply_toEquiv [SMul R α] [SMul R β] (f: SMulEquiv R α β) (x: α) : f.toEquiv x = f x := rfl

variable {α β γ: Type*} [Add α] [Add β] [Add γ] [SMul R α] [SMul R β] [SMul R γ]

@[simp] public theorem LinearEmbedding.apply_toEmbedding (f: α ↪ₗ[R] β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem LinearEquiv.apply_toEquiv (f: α ≃ₗ[R] β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem LinearEmbedding.apply_toLinearHom (f: α ↪ₗ[R] β) (x: α) : f.toLinearHom x = f x := rfl
@[simp] public theorem LinearEquiv.apply_toLinearHom (f: α ≃ₗ[R] β) (x: α) : f.toLinearHom x = f x := rfl

@[ext] public theorem LinearHom.ext (f g: α →ₗ[R] β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem LinearEmbedding.ext (f g: α ↪ₗ[R] β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem LinearEquiv.ext (f g: α ≃ₗ[R] β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def SMulHom.id (R α: Type*) [Add α] [SMul R α] : SMulHom R α α where
  toFun := id
  map_smul _ _ := rfl
@[expose] public protected def LinearHom.id (R α: Type*) [Add α] [SMul R α] : α →ₗ[R] α := {
  AddHom.id α, SMulHom.id R α with
}
@[expose] public protected def LinearEmbedding.id (R α: Type*) [Add α] [SMul R α] : α ↪ₗ[R] α := {
  Embedding.id _, LinearHom.id _ _ with
}
@[expose] public protected def LinearEquiv.id (R α: Type*) [Add α] [SMul R α] : α ≃ₗ[R] α := {
  Equiv.id _, LinearHom.id _ _ with
}

variable {α β γ: Type*} [SMul R α] [SMul R β] [SMul R γ]

@[expose] public def SMulHom.comp (f: SMulHom R β γ) (g: SMulHom R α β) : SMulHom R α γ where
  toFun := f ∘ g
  map_smul k a := by dsimp; rw [map_smul, map_smul]
@[expose] public def SMulEquiv.symm (f: SMulEquiv R α β) : SMulEquiv R β α where
  toEquiv := f.toEquiv.symm
  map_smul k a := by
    dsimp
    apply f.inj; rw [f.symm_apply, apply_toEquiv]
    rw [map_smul, ←apply_toEquiv, f.symm_apply]

variable [Add α] [Add β] [Add γ]

@[expose] public def LinearHom.comp (f: β →ₗ[R] γ) (g: α →ₗ[R] β) : α →ₗ[R] γ := {
  f.toAddHom.comp g.toAddHom, f.toSMulHom.comp g.toSMulHom with
}
@[expose] public def LinearEmbedding.comp (f: β ↪ₗ[R] γ) (g: α ↪ₗ[R] β) : α ↪ₗ[R] γ := {
  f.toEmbedding.comp g.toEmbedding, f.toLinearHom.comp g.toLinearHom with
}
@[expose] public def LinearEquiv.comp (f: β ≃ₗ[R] γ) (g: α ≃ₗ[R] β) : α ≃ₗ[R] γ := {
  f.toEquiv.comp g.toEquiv, f.toLinearHom.comp g.toLinearHom with
}
@[expose] public def LinearEmbedding.trans (f: α ↪ₗ[R] β) (g: β ↪ₗ[R] γ) : α ↪ₗ[R] γ := comp g f
@[expose] public def LinearEquiv.trans (f: α ≃ₗ[R] β) (g: β ≃ₗ[R] γ) : α ≃ₗ[R] γ := comp g f
@[expose] public def LinearEquiv.symm (f: α ≃ₗ[R] β) : β ≃ₗ[R] α := {
  f.toAddEquiv.symm, f.toSMulEquiv.symm with
}

end Api

variable {R S α β γ: Type*} [Add α] [Add β] [Add γ] [SMul R α] [SMul R β] [SMul R γ]

namespace LinearHom

@[simp] public theorem apply_id : LinearHom.id R α x = x := rfl

@[simp] public theorem apply_comp (f: β →ₗ[R] γ) (g: α →ₗ[R] β) (x: α) : f.comp g x = f (g x) := rfl

end LinearHom

namespace LinearEmbedding

@[simp] public theorem apply_id : LinearEmbedding.id R α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪ₗ[R] γ) (g: α ↪ₗ[R] β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪ₗ[R] β) (g: β ↪ₗ[R] γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪ₗ[R] β) : Function.Injective f := f.injective

end LinearEmbedding

namespace LinearEquiv

@[simp] public theorem apply_id : LinearEquiv.id R α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃ₗ[R] β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃ₗ[R] β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃ₗ[R] β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃ₗ[R] γ) (g: α ≃ₗ[R] β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃ₗ[R] β) (g: β ≃ₗ[R] γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃ₗ[R] β) : f.symm.comp f = LinearEquiv.id _ _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃ₗ[R] β) : f.comp f.symm = LinearEquiv.id _ _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃ₗ[R] β) : f.symm.trans f = LinearEquiv.id _ _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃ₗ[R] β) : f.trans f.symm = LinearEquiv.id _ _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃ₗ[R] β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃ₗ[R] β) : Function.Surjective f := f.symm.rightInv.surjective

end LinearEquiv

namespace LinearHom

public instance [Zero β] [IsLawfulZero β] [IsLawfulSMulZero R β] : Zero (LinearHom R α β) where
  zero := {
    toFun _ := 0
    map_add a b := by rw [add_zero]
    map_smul r a := by rw [smul_zero]
  }

public instance [IsRightDistribSMul R β] [IsAddSemigroup β] [IsAddComm β] : Add (LinearHom R α β) where
  add f g := {
    toFun i := f i + g i
    map_add a b := by
      rw [map_add, map_add, add_assoc, ←add_assoc (f b),
        add_comm (f b), ←add_assoc (f a), ←add_assoc (f a),
        add_assoc (_ + _)]
    map_smul r a := by rw [smul_add, map_smul, map_smul]
  }

public instance [SMul S β] [IsSMulComm S R β] [IsRightDistribSMul S β] : SMul S (LinearHom R α β) where
  smul r f := {
    toFun i := r • f i
    map_add a b := by rw [map_add, smul_add]
    map_smul r' a := by rw [map_smul, smul_comm]
  }

variable {β: Type*}
  [SMul R β] [SMul ℕ α]
  [AddMonoidOps β] [IsAddMonoid β] [IsAddComm β]
  [IsLawfulSMulZero R β] [IsRightDistribSMul R β]

public instance : IsAddMonoid (LinearHom R α β) where
  add_assoc _ _ _ := by ext i; apply add_assoc
  add_zero _ := by ext i; apply add_zero
  zero_add _ := by ext i; apply zero_add
  zero_nsmul _ := by ext i; apply zero_nsmul
  succ_nsmul _ _ := by ext i; apply succ_nsmul

public instance : IsAddComm (LinearHom R α β) where
  add_comm f g := by ext; apply add_comm

end LinearHom
