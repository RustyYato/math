module

public import Math.Algebra.Monoid.Defs.Hom
public import Math.Algebra.AddMonoidWithOne.Defs.Basic

namespace Math

section Defs

public structure AddGroupWithOneHom (α β: Type*)
  [Add α] [Zero α] [One α]
  [Add β] [Zero β] [One β] extends α →+ β, α →₁ β where

public structure AddGroupWithOneEmbedding (α β: Type*)
  [Add α] [Zero α] [One α]
  [Add β] [Zero β] [One β] extends α ↪ β, AddGroupWithOneHom α β where

public structure AddGroupWithOneEquiv (α β: Type*)
  [Add α] [Zero α] [One α]
  [Add β] [Zero β] [One β] extends α ≃ β, AddGroupWithOneHom α β,
    α ≃+ β, α ≃₁ β where

infixr:80 " →+₁ " => AddGroupWithOneHom
infixr:80 " ↪+₁ " => AddGroupWithOneEmbedding
infixr:80 " ≃+₁ " => AddGroupWithOneEquiv

end Defs

section Impls

variable [Add α] [Add β] [Zero α] [Zero β] [One α] [One β]

public instance : Funlike (α →+₁ β) α β where
public instance : EmbeddingLike (α ↪+₁ β) α β where
public instance : EquivLike (α ≃+₁ β) α β where

public instance : IsZeroHom (α →+₁ β) α β where
public instance : IsZeroHom (α ↪+₁ β) α β where
public instance : IsZeroHom (α ≃+₁ β) α β where

public instance : IsOneHom (α →+₁ β) α β where
public instance : IsOneHom (α ↪+₁ β) α β where
public instance : IsOneHom (α ≃+₁ β) α β where

public instance : IsAddHom (α →+₁ β) α β where
public instance : IsAddHom (α ↪+₁ β) α β where
public instance : IsAddHom (α ≃+₁ β) α β where

end Impls

variable {α β γ: Type*} [Add α] [Zero α] [One α] [Add β] [Zero β] [One β] [Add γ] [Zero γ] [One γ]

section Reduction

@[simp] public theorem AddGroupWithOneEmbedding.apply_toEmbedding (f: α ↪+₁ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem AddGroupWithOneEquiv.apply_toEquiv (f: α ≃+₁ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem AddGroupWithOneEmbedding.apply_toAddGroupWithOneHom (f: α ↪+₁ β) (x: α) : f.toAddGroupWithOneHom x = f x := rfl
@[simp] public theorem AddGroupWithOneEquiv.apply_toAddGroupWithOneHom (f: α ≃+₁ β) (x: α) : f.toAddGroupWithOneHom x = f x := rfl

@[ext] public theorem AddGroupWithOneHom.ext (f g: α →+₁ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddGroupWithOneEmbedding.ext (f g: α ↪+₁ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddGroupWithOneEquiv.ext (f g: α ≃+₁ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def AddGroupWithOneHom.id (α: Type*) [Add α] [Zero α] [One α] : α →+₁ α := {
  AddGroupHom.id α, OneHom.id α with
}
@[expose] public protected def AddGroupWithOneEmbedding.id (α: Type*) [Add α] [Zero α] [One α] : α ↪+₁ α := {
  Embedding.id _, AddGroupWithOneHom.id _ with
}
@[expose] public protected def AddGroupWithOneEquiv.id (α: Type*) [Add α] [Zero α] [One α] : α ≃+₁ α := {
  Equiv.id _, AddGroupWithOneHom.id _ with
}

@[expose] public def AddGroupWithOneHom.comp (f: β →+₁ γ) (g: α →+₁ β) : α →+₁ γ := {
  f.toAddGroupHom.comp g.toAddGroupHom, f.toOneHom.comp g.toOneHom with
}
@[expose] public def AddGroupWithOneEmbedding.comp (f: β ↪+₁ γ) (g: α ↪+₁ β) : α ↪+₁ γ := {
  f.toEmbedding.comp g.toEmbedding, f.toAddGroupWithOneHom.comp g.toAddGroupWithOneHom with
}
@[expose] public def AddGroupWithOneEquiv.comp (f: β ≃+₁ γ) (g: α ≃+₁ β) : α ≃+₁ γ := {
  f.toEquiv.comp g.toEquiv, f.toAddGroupWithOneHom.comp g.toAddGroupWithOneHom with
}
@[expose] public def AddGroupWithOneEmbedding.trans (f: α ↪+₁ β) (g: β ↪+₁ γ) : α ↪+₁ γ := comp g f
@[expose] public def AddGroupWithOneEquiv.trans (f: α ≃+₁ β) (g: β ≃+₁ γ) : α ≃+₁ γ := comp g f
@[expose] public def AddGroupWithOneEquiv.symm (f: α ≃+₁ β) : β ≃+₁ α := {
  f.toAddGroupEquiv.symm, f.toOneEquiv.symm with
}

end Api

namespace AddGroupWithOneHom

@[simp] public theorem apply_id : AddGroupWithOneHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →+₁ γ) (g: α →+₁ β) (x: α) : f.comp g x = f (g x) := rfl

end AddGroupWithOneHom

namespace AddGroupWithOneEmbedding

@[simp] public theorem apply_id : AddGroupWithOneEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪+₁ γ) (g: α ↪+₁ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪+₁ β) (g: β ↪+₁ γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪+₁ β) : Function.Injective f := f.injective

end AddGroupWithOneEmbedding

namespace AddGroupWithOneEquiv

@[simp] public theorem apply_id : AddGroupWithOneEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃+₁ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃+₁ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃+₁ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃+₁ γ) (g: α ≃+₁ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃+₁ β) (g: β ≃+₁ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃+₁ β) : f.symm.comp f = AddGroupWithOneEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃+₁ β) : f.comp f.symm = AddGroupWithOneEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃+₁ β) : f.symm.trans f = AddGroupWithOneEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃+₁ β) : f.trans f.symm = AddGroupWithOneEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃+₁ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃+₁ β) : Function.Surjective f := f.symm.rightInv.surjective

end AddGroupWithOneEquiv

public theorem map_natCast
  [Funlike F α β]
  [NatCast α] [NatCast β]
  [IsLawfulNatCast α] [IsLawfulNatCast β]
  [IsAddHom F α β] [IsZeroHom F α β] [IsOneHom F α β]
  (f: F) (n: ℕ) : f n = n := by
  induction n with
  | zero => rw [natCast_zero, natCast_zero, map_zero]
  | succ n ih => rw [natCast_succ, natCast_succ, map_add, map_one, ih]
