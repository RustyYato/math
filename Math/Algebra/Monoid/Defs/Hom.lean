module

public import Math.Algebra.Semigroup.Defs.Hom
public import Math.Algebra.Monoid.Defs.Basic

namespace Math

section Defs

public class IsOneHom (F: Type*) (α β: outParam Type*) [Funlike F α β] [One α] [One β] : Prop where
  map_one (f: F) : f 1 = 1 := by intro f; exact f.map_one
public class IsZeroHom (F: Type*) (α β: outParam Type*) [Funlike F α β] [Zero α] [Zero β] : Prop where
  map_zero (f: F) : f 0 = 0 := by intro f; exact f.map_zero
public class IsExpZeroHom (F: Type*) (α β: outParam Type*) [Funlike F α β] [Zero α] [One β] : Prop where
  map_zero_to_one (f: F) : f 0 = 1 := by intro f; exact f.map_zero_to_one
public class IsLogOneHom (F: Type*) (α β: outParam Type*) [Funlike F α β] [One α] [Zero β] : Prop where
  map_one_to_zero (f: F) : f 1 = 0 := by intro f; exact f.map_one_to_zero

export IsOneHom (map_one)
export IsZeroHom (map_zero)
export IsExpZeroHom (map_zero_to_one)
export IsLogOneHom (map_one_to_zero)

public structure OneHom (α β: Type*) [One α] [One β] extends Hom α β where
  protected map_one : toFun 1 = 1
public structure ZeroHom (α β: Type*) [Zero α] [Zero β] extends Hom α β where
  protected map_zero : toFun 0 = 0
public structure ExpZeroHom (α β: Type*) [Zero α] [One β] extends Hom α β where
  protected map_zero_to_one : toFun 0 = 1
public structure LogOneHom (α β: Type*) [One α] [Zero β] extends Hom α β where
  protected map_one_to_zero : toFun 1 = 0

public structure OneEquiv (α β: Type*) [One α] [One β] extends α ≃ β, OneHom α β where
public structure ZeroEquiv (α β: Type*) [Zero α] [Zero β] extends α ≃ β, ZeroHom α β where
public structure ExpZeroEquiv (α β: Type*) [Zero α] [One β] extends α ≃ β, ExpZeroHom α β where
public structure LogOneEquiv (α β: Type*) [One α] [Zero β] extends α ≃ β, LogOneHom α β where

public structure GroupHom (α β: Type*) [Mul α] [One α] [Mul β] [One β] extends MulHom α β, OneHom α β where
public structure AddGroupHom (α β: Type*) [Add α] [Zero α] [Add β] [Zero β] extends AddHom α β, ZeroHom α β where
public structure GroupExpHom (α β: Type*) [Add α] [Zero α] [Mul β] [One β] extends ExpHom α β, ExpZeroHom α β where
public structure GroupLogHom (α β: Type*) [Mul α] [One α] [Add β] [Zero β] extends LogHom α β, LogOneHom α β where

public structure GroupEmbedding (α β: Type*) [Mul α] [One α] [Mul β] [One β] extends α ↪ β, GroupHom α β where
public structure AddGroupEmbedding (α β: Type*) [Add α] [Zero α] [Add β] [Zero β] extends α ↪ β, AddGroupHom α β where
public structure GroupExpEmbedding (α β: Type*) [Add α] [Zero α] [Mul β] [One β] extends α ↪ β, GroupExpHom α β where
public structure GroupLogEmbedding (α β: Type*) [Mul α] [One α] [Add β] [Zero β] extends α ↪ β, GroupLogHom α β where

public structure GroupEquiv (α β: Type*) [Mul α] [One α] [Mul β] [One β] extends α ≃ β, GroupHom α β, MulEquiv α β, OneEquiv α β where
public structure AddGroupEquiv (α β: Type*) [Add α] [Zero α] [Add β] [Zero β] extends α ≃ β, AddGroupHom α β, AddEquiv α β, ZeroEquiv α β where
public structure GroupExpEquiv (α β: Type*) [Add α] [Zero α] [Mul β] [One β] extends α ≃ β, GroupExpHom α β, ExpEquiv α β, ExpZeroEquiv α β where
public structure GroupLogEquiv (α β: Type*) [Mul α] [One α] [Add β] [Zero β] extends α ≃ β, GroupLogHom α β, LogEquiv α β, LogOneEquiv α β where

infixr:80 " →₁ " => OneHom
infixr:80 " →₀ " => ZeroHom
infixr:80 " ≃₁ " => OneEquiv
infixr:80 " ≃₀ " => ZeroEquiv

infixr:80 " →* " => GroupHom
infixr:80 " →+ " => AddGroupHom
infixr:80 " →ₘ+ " => GroupExpHom
infixr:80 " →ₐ* " => GroupLogHom

infixr:80 " ↪* " => GroupEmbedding
infixr:80 " ↪+ " => AddGroupEmbedding
infixr:80 " ↪ₘ+ " => GroupExpEmbedding
infixr:80 " ↪ₐ* " => GroupLogEmbedding

infixr:80 " ≃* " => GroupEquiv
infixr:80 " ≃+ " => AddGroupEquiv
infixr:80 " ≃ₘ+ " => GroupExpEquiv
infixr:80 " ≃ₐ* " => GroupLogEquiv

end Defs

section Impls

variable [Mul α] [Mul β] [Add α] [Add β] [One α] [One β] [Zero α] [Zero β]

public instance : Funlike (OneHom α β) α β where
public instance : Funlike (ZeroHom α β) α β where
public instance : Funlike (ExpZeroHom α β) α β where
public instance : Funlike (LogOneHom α β) α β where
public instance : Funlike (GroupHom α β) α β where
public instance : Funlike (AddGroupHom α β) α β where
public instance : Funlike (GroupExpHom α β) α β where
public instance : Funlike (GroupLogHom α β) α β where

public instance : EmbeddingLike (GroupEmbedding α β) α β where
public instance : EmbeddingLike (AddGroupEmbedding α β) α β where
public instance : EmbeddingLike (GroupExpEmbedding α β) α β where
public instance : EmbeddingLike (GroupLogEmbedding α β) α β where

public instance : EquivLike (OneEquiv α β) α β where
public instance : EquivLike (ZeroEquiv α β) α β where
public instance : EquivLike (ExpZeroEquiv α β) α β where
public instance : EquivLike (LogOneEquiv α β) α β where
public instance : EquivLike (GroupEquiv α β) α β where
public instance : EquivLike (AddGroupEquiv α β) α β where
public instance : EquivLike (GroupExpEquiv α β) α β where
public instance : EquivLike (GroupLogEquiv α β) α β where

public instance : IsOneHom (OneHom α β) α β where
public instance : IsZeroHom (ZeroHom α β) α β where
public instance : IsExpZeroHom (ExpZeroHom α β) α β where
public instance : IsLogOneHom (LogOneHom α β) α β where
public instance : IsOneHom (GroupHom α β) α β where
public instance : IsZeroHom (AddGroupHom α β) α β where
public instance : IsExpZeroHom (GroupExpHom α β) α β where
public instance : IsLogOneHom (GroupLogHom α β) α β where
public instance : IsMulHom (GroupHom α β) α β where
public instance : IsAddHom (AddGroupHom α β) α β where
public instance : IsExpHom (GroupExpHom α β) α β where
public instance : IsLogHom (GroupLogHom α β) α β where

public instance : IsOneHom (GroupEmbedding α β) α β where
public instance : IsZeroHom (AddGroupEmbedding α β) α β where
public instance : IsExpZeroHom (GroupExpEmbedding α β) α β where
public instance : IsLogOneHom (GroupLogEmbedding α β) α β where
public instance : IsMulHom (GroupEmbedding α β) α β where
public instance : IsAddHom (AddGroupEmbedding α β) α β where
public instance : IsExpHom (GroupExpEmbedding α β) α β where
public instance : IsLogHom (GroupLogEmbedding α β) α β where

public instance : IsOneHom (OneEquiv α β) α β where
public instance : IsZeroHom (ZeroEquiv α β) α β where
public instance : IsExpZeroHom (ExpZeroEquiv α β) α β where
public instance : IsLogOneHom (LogOneEquiv α β) α β where
public instance : IsOneHom (GroupEquiv α β) α β where
public instance : IsZeroHom (AddGroupEquiv α β) α β where
public instance : IsExpZeroHom (GroupExpEquiv α β) α β where
public instance : IsLogOneHom (GroupLogEquiv α β) α β where
public instance : IsMulHom (GroupEquiv α β) α β where
public instance : IsAddHom (AddGroupEquiv α β) α β where
public instance : IsExpHom (GroupExpEquiv α β) α β where
public instance : IsLogHom (GroupLogEquiv α β) α β where

end Impls

section AddMul

public instance [Funlike F α β] [Zero α] [Zero β] [IsZeroHom F α β] : IsOneHom (MulOfAdd F) (MulOfAdd α) (MulOfAdd β) where
  map_one := map_zero (F := F) (α := α) (β := β)
public instance [Funlike F α β] [One α] [One β] [IsOneHom F α β] : IsZeroHom (AddOfMul F) (AddOfMul α) (AddOfMul β) where
  map_zero := map_one (F := F) (α := α) (β := β)

end AddMul

section Theorems.One

variable {α β γ: Type*} [One α] [One β] [One γ]

section Reduction

@[simp] public theorem OneEquiv.apply_toEquiv (f: α ≃₁ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem OneEquiv.apply_toOneHom (f: α ≃₁ β) (x: α) : f.toOneHom x = f x := rfl

@[ext] public theorem OneHom.ext (f g: α →₁ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem OneEquiv.ext (f g: α ≃₁ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def OneHom.id (α: Type*) [One α] : α →₁ α where
  toFun := id
  map_one := rfl
@[expose] public protected def OneEquiv.id (α: Type*) [One α] : α ≃₁ α := {
  Equiv.id _, OneHom.id _ with
}

@[expose] public def OneHom.comp (f: β →₁ γ) (g: α →₁ β) : α →₁ γ where
  toFun := f ∘ g
  map_one := by dsimp only [Function.comp_apply]; rw [map_one, map_one]
@[expose] public def OneEquiv.comp (f: β ≃₁ γ) (g: α ≃₁ β) : α ≃₁ γ := {
  f.toEquiv.comp g.toEquiv, f.toOneHom.comp g.toOneHom with
}
@[expose] public def OneEquiv.trans (f: α ≃₁ β) (g: β ≃₁ γ) : α ≃₁ γ := comp g f
@[expose] public def OneEquiv.symm (f: α ≃₁ β) : β ≃₁ α := {
  f.toEquiv.symm with
  map_one := by
    apply f.inj; dsimp only [Equiv.normalize_toFun, apply_toEquiv]
    rw [map_one f]
    rw [←apply_toEquiv, f.symm_apply]
}

end Api

namespace OneHom

@[simp] public theorem apply_id : OneEquiv.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →₁ γ) (g: α →₁ β) (x: α) : f.comp g x = f (g x) := rfl

end OneHom

namespace OneEquiv

@[simp] public theorem apply_id : OneEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃₁ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃₁ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃₁ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃₁ γ) (g: α ≃₁ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃₁ β) (g: β ≃₁ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃₁ β) : f.symm.comp f = OneEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃₁ β) : f.comp f.symm = OneEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃₁ β) : f.symm.trans f = OneEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃₁ β) : f.trans f.symm = OneEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃₁ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃₁ β) : Function.Surjective f := f.symm.rightInv.surjective

end OneEquiv

end Theorems.One

section Theorems.Zero

variable {α β γ: Type*} [Zero α] [Zero β] [Zero γ]

section Reduction

@[simp] public theorem ZeroEquiv.apply_toEquiv (f: α ≃₀ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem ZeroEquiv.apply_toZeroHom (f: α ≃₀ β) (x: α) : f.toZeroHom x = f x := rfl

@[ext] public theorem ZeroHom.ext (f g: α →₀ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem ZeroEquiv.ext (f g: α ≃₀ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def ZeroHom.id (α: Type*) [Zero α] : α →₀ α where
  toFun := id
  map_zero := rfl
@[expose] public protected def ZeroEquiv.id (α: Type*) [Zero α] : α ≃₀ α := {
  Equiv.id _, ZeroHom.id _ with
}

@[expose] public def ZeroHom.comp (f: β →₀ γ) (g: α →₀ β) : α →₀ γ where
  toFun := f ∘ g
  map_zero := by dsimp only [Function.comp_apply]; rw [map_zero, map_zero]
@[expose] public def ZeroEquiv.comp (f: β ≃₀ γ) (g: α ≃₀ β) : α ≃₀ γ := {
  f.toEquiv.comp g.toEquiv, f.toZeroHom.comp g.toZeroHom with
}
@[expose] public def ZeroEquiv.trans (f: α ≃₀ β) (g: β ≃₀ γ) : α ≃₀ γ := comp g f
@[expose] public def ZeroEquiv.symm (f: α ≃₀ β) : β ≃₀ α := {
  f.toEquiv.symm with
  map_zero := by
    apply f.inj; dsimp only [Equiv.normalize_toFun, apply_toEquiv]
    rw [map_zero f]
    rw [←apply_toEquiv, f.symm_apply]
}

end Api

namespace ZeroHom

@[simp] public theorem apply_id : ZeroEquiv.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →₀ γ) (g: α →₀ β) (x: α) : f.comp g x = f (g x) := rfl

end ZeroHom

namespace ZeroEquiv

@[simp] public theorem apply_id : ZeroEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃₀ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃₀ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃₀ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃₀ γ) (g: α ≃₀ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃₀ β) (g: β ≃₀ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃₀ β) : f.symm.comp f = ZeroEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃₀ β) : f.comp f.symm = ZeroEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃₀ β) : f.symm.trans f = ZeroEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃₀ β) : f.trans f.symm = ZeroEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃₀ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃₀ β) : Function.Surjective f := f.symm.rightInv.surjective

end ZeroEquiv

end Theorems.Zero

section Theorems.Group

variable {α β γ: Type*} [Mul α] [One α] [Mul β] [One β] [Mul γ] [One γ]

section Reduction

@[simp] public theorem GroupEmbedding.apply_toEmbedding (f: α ↪* β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem GroupEquiv.apply_toEquiv (f: α ≃* β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem GroupEmbedding.apply_toGroupHom (f: α ↪* β) (x: α) : f.toGroupHom x = f x := rfl
@[simp] public theorem GroupEquiv.apply_toGroupHom (f: α ≃* β) (x: α) : f.toGroupHom x = f x := rfl

@[ext] public theorem GroupHom.ext (f g: α →* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem GroupEmbedding.ext (f g: α ↪* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem GroupEquiv.ext (f g: α ≃* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public def GroupHom.of
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) : α →* β where
  toFun := f
  map_one := map_one f
  map_mul := map_mul f

@[expose] public def GroupEmbedding.of
  [EmbeddingLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) : α ↪* β where
  toEmbedding := f
  map_one := map_one f
  map_mul := map_mul f

@[expose] public def GroupEquiv.of
  [EquivLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) : α ≃* β where
  toEquiv := f
  map_one := map_one f
  map_mul := map_mul f

@[expose] public def GroupHom.copy
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) : α →* β where
  toFun := g
  map_one := by rw [←h, map_one]
  map_mul a b := by rw [←h, ←h, ←h, map_mul]

@[expose] public protected def GroupHom.id (α: Type*) [Mul α] [One α] : α →* α := {
  MulHom.id α, OneHom.id α with
}
@[expose] public protected def GroupEmbedding.id (α: Type*) [Mul α] [One α] : α ↪* α := {
  Embedding.id _, GroupHom.id _ with
}
@[expose] public protected def GroupEquiv.id (α: Type*) [Mul α] [One α] : α ≃* α := {
  Equiv.id _, GroupHom.id _ with
}

@[expose] public def GroupHom.comp (f: β →* γ) (g: α →* β) : α →* γ := {
  f.toMulHom.comp g.toMulHom, f.toOneHom.comp g.toOneHom with
}
@[expose] public def GroupEmbedding.comp (f: β ↪* γ) (g: α ↪* β) : α ↪* γ := {
  f.toEmbedding.comp g.toEmbedding, f.toGroupHom.comp g.toGroupHom with
}
@[expose] public def GroupEquiv.comp (f: β ≃* γ) (g: α ≃* β) : α ≃* γ := {
  f.toEquiv.comp g.toEquiv, f.toGroupHom.comp g.toGroupHom with
}
@[expose] public def GroupEmbedding.trans (f: α ↪* β) (g: β ↪* γ) : α ↪* γ := comp g f
@[expose] public def GroupEquiv.trans (f: α ≃* β) (g: β ≃* γ) : α ≃* γ := comp g f
@[expose] public def GroupEquiv.symm (f: α ≃* β) : β ≃* α := {
  f.toMulEquiv.symm, f.toOneEquiv.symm with
}

@[expose] public def GroupEquiv.mul_of_add_inv_add_of_mul (α: Type*) [Mul α] [One α] : MulOfAdd (AddOfMul α) ≃* α :=
  GroupEquiv.id α
@[expose] public def GroupEquiv.mul_opp₂ (α: Type*) [Mul α] [One α] : αᵐᵒᵖᵐᵒᵖ ≃* α :=
  GroupEquiv.id α

end Api

namespace GroupHom

@[simp] public theorem apply_of
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : GroupHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →* γ) (g: α →* β) (x: α) : f.comp g x = f (g x) := rfl

end GroupHom

namespace GroupEmbedding

@[simp] public theorem apply_of
  [EmbeddingLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : GroupEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪* γ) (g: α ↪* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪* β) (g: β ↪* γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪* β) : Function.Injective f := f.injective

end GroupEmbedding

namespace GroupEquiv

@[simp] public theorem apply_of
  [EquivLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : GroupEquiv.id α x = x := rfl

@[simp] public theorem apply_copy
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) (a: α) : GroupHom.copy f g h a = f a := (h a).symm

@[simp] public theorem apply_symm (f: α ≃* β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃* β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃* β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃* γ) (g: α ≃* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃* β) (g: β ≃* γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃* β) : f.symm.comp f = GroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃* β) : f.comp f.symm = GroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃* β) : f.symm.trans f = GroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃* β) : f.trans f.symm = GroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

attribute [local irreducible] AddOfMul MulOfAdd

@[simp] public theorem apply_mul_of_add_inv_add_of_mul (a: MulOfAdd (AddOfMul α)) : GroupEquiv.mul_of_add_inv_add_of_mul α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_mul_of_add_inv_add_of_mul (a: α) : (GroupEquiv.mul_of_add_inv_add_of_mul α).symm a = .mk (.mk a) :=
  rfl

@[simp] public theorem apply_mul_opp₂ (a: αᵐᵒᵖᵐᵒᵖ) : GroupEquiv.mul_opp₂ α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_mul_opp₂ (a: α) : (GroupEquiv.mul_opp₂ α).symm a = .mk (.mk a) :=
  rfl

public theorem inj (f: α ≃* β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃* β) : Function.Surjective f := f.symm.rightInv.surjective

end GroupEquiv

end Theorems.Group

section Theorems.AddGroup

variable {α β γ: Type*} [Add α] [Zero α] [Add β] [Zero β] [Add γ] [Zero γ]

section Reduction

@[simp] public theorem AddGroupEmbedding.apply_toEmbedding (f: α ↪+ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem AddGroupEquiv.apply_toEquiv (f: α ≃+ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem AddGroupEmbedding.apply_toAddGroupHom (f: α ↪+ β) (x: α) : f.toAddGroupHom x = f x := rfl
@[simp] public theorem AddGroupEquiv.apply_toAddGroupHom (f: α ≃+ β) (x: α) : f.toAddGroupHom x = f x := rfl

@[ext] public theorem AddGroupHom.ext (f g: α →+ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddGroupEmbedding.ext (f g: α ↪+ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddGroupEquiv.ext (f g: α ≃+ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public def AddGroupHom.of
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) : α →+ β where
  toFun := f
  map_zero := map_zero f
  map_add := map_add f

@[expose] public def AddGroupEmbedding.of
  [EmbeddingLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) : α ↪+ β where
  toEmbedding := f
  map_zero := map_zero f
  map_add := map_add f

@[expose] public def AddGroupEquiv.of
  [EquivLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) : α ≃+ β where
  toEquiv := f
  map_zero := map_zero f
  map_add := map_add f

@[expose] public def AddGroupHom.copy
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) : α →+ β where
  toFun := g
  map_zero := by rw [←h, map_zero]
  map_add a b := by rw [←h, ←h, ←h, map_add]

@[expose] public protected def AddGroupHom.id (α: Type*) [Add α] [Zero α] : α →+ α := {
  AddHom.id α, ZeroHom.id α with
}
@[expose] public protected def AddGroupEmbedding.id (α: Type*) [Add α] [Zero α] : α ↪+ α := {
  Embedding.id _, AddGroupHom.id _ with
}
@[expose] public protected def AddGroupEquiv.id (α: Type*) [Add α] [Zero α] : α ≃+ α := {
  Equiv.id _, AddGroupHom.id _ with
}

@[expose] public def AddGroupHom.comp (f: β →+ γ) (g: α →+ β) : α →+ γ := {
  f.toAddHom.comp g.toAddHom, f.toZeroHom.comp g.toZeroHom with
}
@[expose] public def AddGroupEmbedding.comp (f: β ↪+ γ) (g: α ↪+ β) : α ↪+ γ := {
  f.toEmbedding.comp g.toEmbedding, f.toAddGroupHom.comp g.toAddGroupHom with
}
@[expose] public def AddGroupEquiv.comp (f: β ≃+ γ) (g: α ≃+ β) : α ≃+ γ := {
  f.toEquiv.comp g.toEquiv, f.toAddGroupHom.comp g.toAddGroupHom with
}
@[expose] public def AddGroupEmbedding.trans (f: α ↪+ β) (g: β ↪+ γ) : α ↪+ γ := comp g f
@[expose] public def AddGroupEquiv.trans (f: α ≃+ β) (g: β ≃+ γ) : α ≃+ γ := comp g f
@[expose] public def AddGroupEquiv.symm (f: α ≃+ β) : β ≃+ α := {
  f.toAddEquiv.symm, f.toZeroEquiv.symm with
}

@[expose] public def AddGroupEquiv.add_of_mul_inv_mul_of_add (α: Type*) [Add α] [Zero α] : AddOfMul (MulOfAdd α) ≃+ α :=
  AddGroupEquiv.id α
@[expose] public def AddGroupEquiv.add_opp₂ (α: Type*) [Add α] [Zero α] : αᵃᵒᵖᵃᵒᵖ ≃+ α :=
  AddGroupEquiv.id α

end Api

namespace AddGroupHom

@[simp] public theorem apply_of
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_copy
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) (a: α) : copy f g h a = f a := (h a).symm

@[simp] public theorem apply_id : AddGroupHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →+ γ) (g: α →+ β) (x: α) : f.comp g x = f (g x) := rfl

end AddGroupHom

namespace AddGroupEmbedding

@[simp] public theorem apply_of
  [EmbeddingLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : AddGroupEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪+ γ) (g: α ↪+ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪+ β) (g: β ↪+ γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪+ β) : Function.Injective f := f.injective

end AddGroupEmbedding

namespace AddGroupEquiv

@[simp] public theorem apply_of
  [EquivLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : AddGroupEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃+ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃+ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃+ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃+ γ) (g: α ≃+ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃+ β) (g: β ≃+ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃+ β) : f.symm.comp f = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃+ β) : f.comp f.symm = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃+ β) : f.symm.trans f = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃+ β) : f.trans f.symm = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

attribute [local irreducible] AddOfMul MulOfAdd

@[simp] public theorem apply_add_of_mul_inv_mul_of_add (a: AddOfMul (MulOfAdd α)) : AddGroupEquiv.add_of_mul_inv_mul_of_add α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_add_of_mul_inv_mul_of_add (a: α) : (AddGroupEquiv.add_of_mul_inv_mul_of_add α).symm a = .mk (.mk a) :=
  rfl

@[simp] public theorem apply_mul_opp₂ (a: αᵃᵒᵖᵃᵒᵖ) : add_opp₂ α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_mul_opp₂ (a: α) : (add_opp₂ α).symm a = .mk (.mk a) :=
  rfl

public theorem inj (f: α ≃+ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃+ β) : Function.Surjective f := f.symm.rightInv.surjective

end AddGroupEquiv

end Theorems.AddGroup

namespace Automorphism

variable [MonoidOps α] [IsMonoid α] [AddMonoidOps α] [IsAddMonoid α]

public scoped instance : One (α ≃* α) where
  one := .id _
public scoped instance : Mul (α ≃* α) where
  mul := .comp

public scoped instance : IsLawfulOne (α ≃* α) where
  mul_one _ := rfl
  one_mul _ := rfl

public scoped instance : IsSemigroup (α ≃* α) where
  mul_assoc _ _ _ := rfl

public scoped instance : Pow (α ≃* α) ℕ := DefaultPowN.instPowNat
public scoped instance : IsLawfulPowN (α ≃* α) := DefaultPowN.instIsLawfulPowN
public scoped instance : IsMonoid (α ≃* α) where

public scoped instance : One (α ≃+ α) where
  one := .id _
public scoped instance : Mul (α ≃+ α) where
  mul := .comp

public scoped instance : IsLawfulOne (α ≃+ α) where
  mul_one _ := rfl
  one_mul _ := rfl

public scoped instance : IsSemigroup (α ≃+ α) where
  mul_assoc _ _ _ := rfl

public scoped instance : Pow (α ≃+ α) ℕ := DefaultPowN.instPowNat
public scoped instance : IsLawfulPowN (α ≃+ α) := DefaultPowN.instIsLawfulPowN
public scoped instance : IsMonoid (α ≃+ α) where

end Automorphism

public theorem map_pown [Funlike F α β]
  [MonoidOps α] [MonoidOps β]
  [IsLawfulPowN α] [IsLawfulPowN β]
  [IsMulHom F α β] [IsOneHom F α β]
  (f: F) (a: α) (n: ℕ) : f (a ^ n) = f a ^ n := by
  induction n with
  | zero => rw [pown_zero, pown_zero, map_one]
  | succ n ih => rw [pown_succ, pown_succ, map_mul, ih]

public theorem map_nsmul [Funlike F α β]
  [AddMonoidOps α] [AddMonoidOps β]
  [IsLawfulNSMul α] [IsLawfulNSMul β]
  [IsAddHom F α β] [IsZeroHom F α β]
  (f: F) (a: α) (n: ℕ) : f (n • a) = n • f a :=
  map_pown (MulOfAdd.mk f) (MulOfAdd.mk a) n

@[expose] public def nsmul_hom [AddMonoidOps α] [IsAddMonoid α] (a: α) : ℕ →+ α where
  toFun n := n • a
  map_zero := by rw [zero_nsmul]
  map_add n m := by
    induction m with
    | zero => rw [add_zero, zero_nsmul, add_zero]
    | succ m ih => rw [Nat.add_succ, succ_nsmul, succ_nsmul, ←add_assoc, ih]

@[expose] public def pown_hom [MonoidOps α] [IsMonoid α] (a: α) : ℕ →ₘ+ α where
  toFun n := a ^ n
  map_zero_to_one := map_zero (β := AddOfMul α) (nsmul_hom (AddOfMul.mk a))
  map_add_to_mul := map_add (β := AddOfMul α) (nsmul_hom (AddOfMul.mk a))
