module

public import Math.Data.Embedding.Defs
public import Math.Data.Surjection.Defs
public import Math.Data.Equiv.Defs

public import Math.Algebra.Semigroup.Defs.Basic

namespace Math
section Defs

public class IsMulHom (F α β: Type*) [Funlike F α β] [Mul α] [Mul β] : Prop where
  map_mul (f: F) (a b: α) : f (a * b) = f a * f b := by intro f; exact f.map_mul
public class IsAddHom (F α β: Type*) [Funlike F α β] [Add α] [Add β] : Prop where
  map_add (f: F) (a b: α) : f (a + b) = f a + f b := by intro f; exact f.map_add
public class IsExpHom (F α β: Type*) [Funlike F α β] [Add α] [Mul β] : Prop where
  map_add_to_mul (f: F) (a b: α) : f (a + b) = f a * f b := by intro f; exact f.map_add_to_mul
public class IsLogHom (F α β: Type*) [Funlike F α β] [Mul α] [Add β] : Prop where
  map_mul_to_add (f: F) (a b: α) : f (a * b) = f a + f b := by intro f; exact f.map_mul_to_add

export IsMulHom (map_mul)
export IsAddHom (map_add)
export IsExpHom (map_add_to_mul)
export IsLogHom (map_mul_to_add)

public structure MulHom (α β: Type*) [Mul α] [Mul β] extends Hom α β where
  protected map_mul (a b: α) : toFun (a * b) = toFun a * toFun b
public structure AddHom (α β: Type*) [Add α] [Add β] extends Hom α β where
  protected map_add (a b: α) : toFun (a + b) = toFun a + toFun b
public structure ExpHom (α β: Type*) [Add α] [Mul β] extends Hom α β where
  protected map_add_to_mul (a b: α) : toFun (a + b) = toFun a * toFun b
public structure LogHom (α β: Type*) [Mul α] [Add β] extends Hom α β where
  protected map_mul_to_add (a b: α) : toFun (a * b) = toFun a + toFun b

public structure MulEmbedding (α β: Type*) [Mul α] [Mul β] extends α ↪ β, MulHom α β where
public structure AddEmbedding (α β: Type*) [Add α] [Add β] extends α ↪ β, AddHom α β where
public structure ExpEmbedding (α β: Type*) [Add α] [Mul β] extends α ↪ β, ExpHom α β where
public structure LogEmbedding (α β: Type*) [Mul α] [Add β] extends α ↪ β, LogHom α β where

public structure MulSurjection (α β: Type*) [Mul α] [Mul β] extends α ↠ β, MulHom α β where
public structure AddSurjection (α β: Type*) [Add α] [Add β] extends α ↠ β, AddHom α β where
public structure ExpSurjection (α β: Type*) [Add α] [Mul β] extends α ↠ β, ExpHom α β where
public structure LogSurjection (α β: Type*) [Mul α] [Add β] extends α ↠ β, LogHom α β where

public structure MulEquiv (α β: Type*) [Mul α] [Mul β] extends α ≃ β, MulHom α β where
public structure AddEquiv (α β: Type*) [Add α] [Add β] extends α ≃ β, AddHom α β where
public structure ExpEquiv (α β: Type*) [Add α] [Mul β] extends α ≃ β, ExpHom α β where
public structure LogEquiv (α β: Type*) [Mul α] [Add β] extends α ≃ β, LogHom α β where

infixr:80 " →*ₙ " => MulHom
infixr:80 " →+ₙ " => AddHom
infixr:80 " →ₘ+ₙ " => LogHom
infixr:80 " →ₐ*ₙ " => ExpHom

infixr:80 " ↪*ₙ " => MulEmbedding
infixr:80 " ↪+ₙ " => AddEmbedding
infixr:80 " ↪ₘ+ₙ " => LogEmbedding
infixr:80 " ↪ₐ*ₙ " => ExpEmbedding

infixr:80 " ↠*ₙ " => MulSurjection
infixr:80 " ↠+ₙ " => AddSurjection
infixr:80 " ↠ₘ+ₙ " => LogSurjection
infixr:80 " ↠ₐ*ₙ " => ExpSurjection

infixr:80 " ≃*ₙ " => MulEquiv
infixr:80 " ≃+ₙ " => AddEquiv
infixr:80 " ≃ₘ+ₙ " => LogEquiv
infixr:80 " ≃ₐ*ₙ " => ExpEquiv

end Defs

section Impls

variable {α β γ: Type*} [Mul α] [Mul β] [Mul γ] [Add α] [Add β] [Add γ]

public instance : Funlike (α →*ₙ β) α β where
public instance : Funlike (α →+ₙ β) α β where
public instance : Funlike (α →ₘ+ₙ β) α β where
public instance : Funlike (α →ₐ*ₙ β) α β where
public instance : IsMulHom (α →*ₙ β) α β where
public instance : IsAddHom (α →+ₙ β) α β where
public instance : IsLogHom (α →ₘ+ₙ β) α β where
public instance : IsExpHom (α →ₐ*ₙ β) α β where

public instance : EmbeddingLike (α ↪*ₙ β) α β where
public instance : EmbeddingLike (α ↪+ₙ β) α β where
public instance : EmbeddingLike (α ↪ₘ+ₙ β) α β where
public instance : EmbeddingLike (α ↪ₐ*ₙ β) α β where
public instance : IsMulHom (α ↪*ₙ β) α β where
public instance : IsAddHom (α ↪+ₙ β) α β where
public instance : IsLogHom (α ↪ₘ+ₙ β) α β where
public instance : IsExpHom (α ↪ₐ*ₙ β) α β where

public instance : SurjectionLike (α ↠*ₙ β) α β where
public instance : SurjectionLike (α ↠+ₙ β) α β where
public instance : SurjectionLike (α ↠ₘ+ₙ β) α β where
public instance : SurjectionLike (α ↠ₐ*ₙ β) α β where
public instance : IsMulHom (α ↠*ₙ β) α β where
public instance : IsAddHom (α ↠+ₙ β) α β where
public instance : IsLogHom (α ↠ₘ+ₙ β) α β where
public instance : IsExpHom (α ↠ₐ*ₙ β) α β where

public instance : EquivLike (α ≃*ₙ β) α β where
public instance : EquivLike (α ≃+ₙ β) α β where
public instance : EquivLike (α ≃ₘ+ₙ β) α β where
public instance : EquivLike (α ≃ₐ*ₙ β) α β where
public instance : IsMulHom (α ≃*ₙ β) α β where
public instance : IsAddHom (α ≃+ₙ β) α β where
public instance : IsLogHom (α ≃ₘ+ₙ β) α β where
public instance : IsExpHom (α ≃ₐ*ₙ β) α β where

end Impls

section AddMul

public instance [Funlike F α β] : Funlike (MulOfAdd F) (MulOfAdd α) (MulOfAdd β) where
  coeFun f a := .mk (f.get a.get)
  coeInj := DFunlike.coeInj (F := F) (α := α) (β := fun _ => β)

public instance [Funlike F α β] : Funlike (AddOfMul F) (AddOfMul α) (AddOfMul β) where
  coeFun f a := .mk (f.get a.get)
  coeInj := DFunlike.coeInj (F := F) (α := α) (β := fun _ => β)

public instance [Funlike F α β] [Add α] [Add β] [IsAddHom F α β] : IsMulHom (MulOfAdd F) (MulOfAdd α) (MulOfAdd β) where
  map_mul := map_add (F := F) (α := α) (β := β)
public instance [Funlike F α β] [Mul α] [Mul β] [IsMulHom F α β] : IsAddHom (AddOfMul F) (AddOfMul α) (AddOfMul β) where
  map_add := map_mul (F := F) (α := α) (β := β)

attribute [local irreducible] AddOfMul MulOfAdd

@[simp] public theorem apply_add_of_mul [Funlike F α β] (f: AddOfMul F) (a: AddOfMul α) : f a = .mk (f.get a.get) := rfl
@[simp] public theorem apply_mul_of_add [Funlike F α β] (f: MulOfAdd F) (a: MulOfAdd α) : f a = .mk (f.get a.get) := rfl

end AddMul

section Theorems.Mul

variable {α β γ: Type*} [Mul α] [Mul β] [Mul γ]

section Reduction

@[simp] public theorem MulEmbedding.apply_toEmbedding (f: α ↪*ₙ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem MulEquiv.apply_toEquiv (f: α ≃*ₙ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem MulEmbedding.apply_toMulHom (f: α ↪*ₙ β) (x: α) : f.toMulHom x = f x := rfl
@[simp] public theorem MulEquiv.apply_toMulHom (f: α ≃*ₙ β) (x: α) : f.toMulHom x = f x := rfl

@[ext] public theorem MulHom.ext (f g: α →*ₙ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem MulEmbedding.ext (f g: α ↪*ₙ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem MulEquiv.ext (f g: α ≃*ₙ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def MulHom.id (α: Type*) [Mul α] : α →*ₙ α where
  toFun := id
  map_mul _ _ := rfl
@[expose] public protected def MulEmbedding.id (α: Type*) [Mul α] : α ↪*ₙ α := {
  Embedding.id _, MulHom.id _ with
}
@[expose] public protected def MulSurjection.id (α: Type*) [Mul α] : α ↠*ₙ α := {
  Surjection.id _, MulHom.id _ with
}
@[expose] public protected def MulEquiv.id (α: Type*) [Mul α] : α ≃*ₙ α := {
  Equiv.id _, MulHom.id _ with
}

@[expose] public def MulHom.comp (f: β →*ₙ γ) (g: α →*ₙ β) : α →*ₙ γ where
  toFun := f ∘ g
  map_mul a b := by dsimp only [Function.comp_apply]; rw [map_mul, map_mul]
@[expose] public def MulEmbedding.comp (f: β ↪*ₙ γ) (g: α ↪*ₙ β) : α ↪*ₙ γ := {
  f.toEmbedding.comp g.toEmbedding, f.toMulHom.comp g.toMulHom with
}
@[expose] public def MulSurjection.comp (f: β ↠*ₙ γ) (g: α ↠*ₙ β) : α ↠*ₙ γ := {
  f.toSurjection.comp g.toSurjection, f.toMulHom.comp g.toMulHom with
}
@[expose] public def MulEquiv.comp (f: β ≃*ₙ γ) (g: α ≃*ₙ β) : α ≃*ₙ γ := {
  f.toEquiv.comp g.toEquiv, f.toMulHom.comp g.toMulHom with
}
@[expose] public def MulEmbedding.trans (f: α ↪*ₙ β) (g: β ↪*ₙ γ) : α ↪*ₙ γ := comp g f
@[expose] public def MulSurjection.trans (f: α ↠*ₙ β) (g: β ↠*ₙ γ) : α ↠*ₙ γ := comp g f
@[expose] public def MulEquiv.trans (f: α ≃*ₙ β) (g: β ≃*ₙ γ) : α ≃*ₙ γ := comp g f
@[expose] public def MulEquiv.symm (f: α ≃*ₙ β) : β ≃*ₙ α := {
  f.toEquiv.symm with
  map_mul a b := by
    apply f.inj; dsimp only [Equiv.normalize_toFun, apply_toEquiv]
    rw [map_mul f]
    iterate 3 rw [←apply_toEquiv, f.symm_apply]
}

end Api

namespace MulHom

@[simp] public theorem apply_id : MulHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →*ₙ γ) (g: α →*ₙ β) (x: α) : f.comp g x = f (g x) := rfl

end MulHom

namespace MulEmbedding

@[simp] public theorem apply_id : MulEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪*ₙ γ) (g: α ↪*ₙ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪*ₙ β) (g: β ↪*ₙ γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪*ₙ β) : Function.Injective f := f.injective

end MulEmbedding

namespace MulSurjection

@[simp] public theorem apply_id : MulSurjection.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↠*ₙ γ) (g: α ↠*ₙ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↠*ₙ β) (g: β ↠*ₙ γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem surj (f: α ↠*ₙ β) : Function.Surjective f := f.surjective

end MulSurjection

namespace MulEquiv

@[simp] public theorem apply_id : MulEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃*ₙ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃*ₙ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃*ₙ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃*ₙ γ) (g: α ≃*ₙ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃*ₙ β) (g: β ≃*ₙ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃*ₙ β) : f.symm.comp f = MulEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃*ₙ β) : f.comp f.symm = MulEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃*ₙ β) : f.symm.trans f = MulEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃*ₙ β) : f.trans f.symm = MulEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃*ₙ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃*ₙ β) : Function.Surjective f := f.symm.rightInv.surjective

end MulEquiv

end Theorems.Mul

section Theorems.Add

variable {α β γ: Type*} [Add α] [Add β] [Add γ]

section Reduction

@[simp] public theorem AddEmbedding.apply_toEmbedding (f: α ↪+ₙ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem AddEquiv.apply_toEquiv (f: α ≃+ₙ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem AddEmbedding.apply_toAddHom (f: α ↪+ₙ β) (x: α) : f.toAddHom x = f x := rfl
@[simp] public theorem AddEquiv.apply_toAddHom (f: α ≃+ₙ β) (x: α) : f.toAddHom x = f x := rfl

@[ext] public theorem AddHom.ext (f g: α →+ₙ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddEmbedding.ext (f g: α ↪+ₙ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddEquiv.ext (f g: α ≃+ₙ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def AddHom.id (α: Type*) [Add α] : α →+ₙ α where
  toFun := id
  map_add _ _ := rfl
@[expose] public protected def AddEmbedding.id (α: Type*) [Add α] : α ↪+ₙ α := {
  Embedding.id _, AddHom.id _ with
}
@[expose] public protected def AddSurjection.id (α: Type*) [Add α] : α ↠+ₙ α := {
  Surjection.id _, AddHom.id _ with
}
@[expose] public protected def AddEquiv.id (α: Type*) [Add α] : α ≃+ₙ α := {
  Equiv.id _, AddHom.id _ with
}

@[expose] public def AddHom.comp (f: β →+ₙ γ) (g: α →+ₙ β) : α →+ₙ γ where
  toFun := f ∘ g
  map_add a b := by dsimp only [Function.comp_apply]; rw [map_add, map_add]
@[expose] public def AddEmbedding.comp (f: β ↪+ₙ γ) (g: α ↪+ₙ β) : α ↪+ₙ γ := {
  f.toEmbedding.comp g.toEmbedding, f.toAddHom.comp g.toAddHom with
}
@[expose] public def AddSurjection.comp (f: β ↠+ₙ γ) (g: α ↠+ₙ β) : α ↠+ₙ γ := {
  f.toSurjection.comp g.toSurjection, f.toAddHom.comp g.toAddHom with
}
@[expose] public def AddEquiv.comp (f: β ≃+ₙ γ) (g: α ≃+ₙ β) : α ≃+ₙ γ := {
  f.toEquiv.comp g.toEquiv, f.toAddHom.comp g.toAddHom with
}
@[expose] public def AddEmbedding.trans (f: α ↪+ₙ β) (g: β ↪+ₙ γ) : α ↪+ₙ γ := comp g f
@[expose] public def AddSurjection.trans (f: α ↠+ₙ β) (g: β ↠+ₙ γ) : α ↠+ₙ γ := comp g f
@[expose] public def AddEquiv.trans (f: α ≃+ₙ β) (g: β ≃+ₙ γ) : α ≃+ₙ γ := comp g f
@[expose] public def AddEquiv.symm (f: α ≃+ₙ β) : β ≃+ₙ α := {
  f.toEquiv.symm with
  map_add a b := by
    apply f.inj; dsimp only [Equiv.normalize_toFun, apply_toEquiv]
    rw [map_add f]
    iterate 3 rw [←apply_toEquiv, f.symm_apply]
}

end Api

namespace AddHom

@[simp] public theorem apply_id : AddHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →+ₙ γ) (g: α →+ₙ β) (x: α) : f.comp g x = f (g x) := rfl

end AddHom

namespace AddEmbedding

@[simp] public theorem apply_id : AddEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪+ₙ γ) (g: α ↪+ₙ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪+ₙ β) (g: β ↪+ₙ γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪+ₙ β) : Function.Injective f := f.injective

end AddEmbedding

namespace AddSurjection

@[simp] public theorem apply_id : AddSurjection.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↠+ₙ γ) (g: α ↠+ₙ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↠+ₙ β) (g: β ↠+ₙ γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem surj (f: α ↠+ₙ β) : Function.Surjective f := f.surjective

end AddSurjection

namespace AddEquiv

@[simp] public theorem apply_id : AddEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃+ₙ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃+ₙ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃+ₙ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃+ₙ γ) (g: α ≃+ₙ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃+ₙ β) (g: β ≃+ₙ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃+ₙ β) : f.symm.comp f = AddEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃+ₙ β) : f.comp f.symm = AddEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃+ₙ β) : f.symm.trans f = AddEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃+ₙ β) : f.trans f.symm = AddEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃+ₙ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃+ₙ β) : Function.Surjective f := f.symm.rightInv.surjective

end AddEquiv

end Theorems.Add
