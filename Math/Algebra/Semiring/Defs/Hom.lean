module

public import Math.Algebra.AddMonoidWithOne.Defs.Hom
public import Math.Algebra.Semiring.Defs.Basic

import Math.Algebra.AddMonoidWithOne.Defs.Lemmas

namespace Math

section Defs

public structure RingHom (α β: Type*)
  [Add α] [Mul α] [Zero α] [One α]
  [Add β] [Mul β] [Zero β] [One β] extends α →+ β, α →* β where

public structure RingEmbedding (α β: Type*)
  [Add α] [Mul α] [Zero α] [One α]
  [Add β] [Mul β] [Zero β] [One β] extends α ↪ β, RingHom α β where

public structure RingEquiv (α β: Type*)
  [Add α] [Mul α] [Zero α] [One α]
  [Add β] [Mul β] [Zero β] [One β] extends α ≃ β, RingHom α β,
    α ≃+ β, α ≃* β where

infixr:80 " →+* " => RingHom
infixr:80 " ↪+* " => RingEmbedding
infixr:80 " ≃+* " => RingEquiv

end Defs

section Impls

variable [Add α] [Add β] [Mul α] [Mul β] [Zero α] [Zero β] [One α] [One β]

public instance : Funlike (α →+* β) α β where
public instance : EmbeddingLike (α ↪+* β) α β where
public instance : EquivLike (α ≃+* β) α β where

public instance : IsZeroHom (α →+* β) α β where
public instance : IsZeroHom (α ↪+* β) α β where
public instance : IsZeroHom (α ≃+* β) α β where

public instance : IsOneHom (α →+* β) α β where
public instance : IsOneHom (α ↪+* β) α β where
public instance : IsOneHom (α ≃+* β) α β where

public instance : IsAddHom (α →+* β) α β where
public instance : IsAddHom (α ↪+* β) α β where
public instance : IsAddHom (α ≃+* β) α β where

public instance : IsMulHom (α →+* β) α β where
public instance : IsMulHom (α ↪+* β) α β where
public instance : IsMulHom (α ≃+* β) α β where

end Impls

section

variable {α β γ: Type*} [Add α] [Mul α] [Zero α] [One α] [Add β] [Mul β] [Zero β] [One β] [Add γ] [Mul γ] [Zero γ] [One γ]

section Reduction

@[simp] public theorem RingEmbedding.apply_toEmbedding (f: α ↪+* β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem RingEquiv.apply_toEquiv (f: α ≃+* β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem RingEmbedding.apply_toRingHom (f: α ↪+* β) (x: α) : f.toRingHom x = f x := rfl
@[simp] public theorem RingEquiv.apply_toRingHom (f: α ≃+* β) (x: α) : f.toRingHom x = f x := rfl

@[ext] public theorem RingHom.ext (f g: α →+* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem RingEmbedding.ext (f g: α ↪+* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem RingEquiv.ext (f g: α ≃+* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def RingHom.id (α: Type*) [Add α] [Mul α] [Zero α] [One α] : α →+* α := {
  AddGroupHom.id α, GroupHom.id α with
}
@[expose] public protected def RingEmbedding.id (α: Type*) [Add α] [Mul α] [Zero α] [One α] : α ↪+* α := {
  Embedding.id _, RingHom.id _ with
}
@[expose] public protected def RingEquiv.id (α: Type*) [Add α] [Mul α] [Zero α] [One α] : α ≃+* α := {
  Equiv.id _, RingHom.id _ with
}

@[expose] public def RingHom.comp (f: β →+* γ) (g: α →+* β) : α →+* γ := {
  f.toAddGroupHom.comp g.toAddGroupHom, f.toGroupHom.comp g.toGroupHom with
}
@[expose] public def RingEmbedding.comp (f: β ↪+* γ) (g: α ↪+* β) : α ↪+* γ := {
  f.toEmbedding.comp g.toEmbedding, f.toRingHom.comp g.toRingHom with
}
@[expose] public def RingEquiv.comp (f: β ≃+* γ) (g: α ≃+* β) : α ≃+* γ := {
  f.toEquiv.comp g.toEquiv, f.toRingHom.comp g.toRingHom with
}
@[expose] public def RingEmbedding.trans (f: α ↪+* β) (g: β ↪+* γ) : α ↪+* γ := comp g f
@[expose] public def RingEquiv.trans (f: α ≃+* β) (g: β ≃+* γ) : α ≃+* γ := comp g f
@[expose] public def RingEquiv.symm (f: α ≃+* β) : β ≃+* α := {
  f.toAddGroupEquiv.symm, f.toGroupEquiv.symm with
}

end Api

namespace RingHom

@[simp] public theorem apply_id : RingHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →+* γ) (g: α →+* β) (x: α) : f.comp g x = f (g x) := rfl

end RingHom

namespace RingEmbedding

@[simp] public theorem apply_id : RingEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪+* γ) (g: α ↪+* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪+* β) (g: β ↪+* γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪+* β) : Function.Injective f := f.injective

end RingEmbedding

namespace RingEquiv

@[simp] public theorem apply_id : RingEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃+* β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃+* β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃+* β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃+* γ) (g: α ≃+* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃+* β) (g: β ≃+* γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃+* β) : f.symm.comp f = RingEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃+* β) : f.comp f.symm = RingEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃+* β) : f.symm.trans f = RingEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃+* β) : f.trans f.symm = RingEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃+* β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃+* β) : Function.Surjective f := f.symm.rightInv.surjective

end RingEquiv

end

variable [SemiringOps α] [IsSemiring α]

@[expose] public def RingHom.natCast [IsSemiring α] : ℕ →+* α where
  toFun := Nat.cast
  map_zero := by exact natCast_zero
  map_one := by exact natCast_one
  map_add := by exact natCast_add
  map_mul := by exact natCast_mul

@[simp] public theorem RingHom.apply_natCast (n: ℕ) : RingHom.natCast n = (n: α) := rfl

public instance : Subsingleton (ℕ →+* α) where
  allEq := by
    suffices ∀f: ℕ →+* α, f = RingHom.natCast by
      intro a b; rw [this a, this b]
    intro f; ext z
    show f (Nat.cast z) = _
    rw [RingHom.apply_natCast, map_natCast]
