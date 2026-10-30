module

public import Math.Tactic.Basic
public import Math.Data.AddMul.Defs
public import Math.Data.Embedding.Defs

namespace Math

section Property

public class IsSemigroup (α: Type*) [Mul α] : Prop where
  mul_assoc (a b c: α) : a * b * c = a * (b * c)

export IsSemigroup (mul_assoc)

public class IsAddSemigroup (α: Type*) [Add α] : Prop where
  add_assoc (a b c: α) : a + b + c = a + (b + c)

export IsAddSemigroup (add_assoc)

public class IsCommAt {α: Type*} [Mul α] (a b: α) where
  mul_comm: a * b = b * a
public class IsAddCommAt {α: Type*} [Add α] (a b: α) where
  add_comm: a + b = b + a

public class IsComm (α: Type*) [Mul α] where
  mul_comm (a b: α): a * b = b * a
public class IsAddComm (α: Type*) [Add α] where
  add_comm (a b: α): a + b = b + a

public instance (priority := 10_000) [Mul α] [IsComm α] (a b: α) : IsCommAt a b where
  mul_comm := IsComm.mul_comm _ _
public instance (priority := 10_000) [Add α] [IsAddComm α] (a b: α) : IsAddCommAt a b where
  add_comm := IsAddComm.add_comm _ _

public theorem mul_comm [Mul α] (a b: α) [IsCommAt a b] : a * b = b * a := IsCommAt.mul_comm
public theorem add_comm [Add α] (a b: α) [IsAddCommAt a b] : a + b = b + a := IsAddCommAt.add_comm

public instance (priority := 10) [Mul α] (a b: α) [IsCommAt a b] : IsCommAt b a where
  mul_comm := by
    rw [mul_comm a]

public instance (priority := 10) [Add α] (a b: α) [IsAddCommAt a b] : IsAddCommAt b a where
  add_comm := by
    rw [add_comm a]

public class IsLeftCancel (α: Type*) [Mul α] where
  of_mul_left {k a b: α} : k * a = k * b -> a = b
public class IsRightCancel (α: Type*) [Mul α] where
  of_mul_right {k a b: α} : a * k = b * k -> a = b

export IsLeftCancel (of_mul_left)
export IsRightCancel (of_mul_right)

public class IsLeftAddCancel (α: Type*) [Add α] where
  of_add_left {k a b: α} : k + a = k + b -> a = b
public class IsRightAddCancel (α: Type*) [Add α] where
  of_add_right {k a b: α} : a + k = b + k -> a = b

export IsLeftAddCancel (of_add_left)
export IsRightAddCancel (of_add_right)

public class IsLeftCancel₀ (α: Type*) [Mul α] [Zero α] where
  of_mul_left₀ {k a b: α} : k ≠ 0 -> k * a = k * b -> a = b
public class IsRightCancel₀ (α: Type*) [Mul α] [Zero α] where
  of_mul_right₀ {k a b: α} : k ≠ 0 -> a * k = b * k -> a = b

export IsLeftCancel₀ (of_mul_left₀)
export IsRightCancel₀ (of_mul_right₀)

public instance (priority := 500) [Mul α] [IsRightCancel α] [IsComm α] : IsLeftCancel α where
  of_mul_left {k a b} h := by
    rw [mul_comm k, mul_comm k] at h
    exact of_mul_right h
public instance (priority := 500) [Mul α] [IsLeftCancel α] [IsComm α] : IsRightCancel α where
  of_mul_right {k a b} h := by
    rw [mul_comm _ k, mul_comm _ k] at h
    exact of_mul_left h

public instance (priority := 500) [Add α] [IsRightAddCancel α] [IsAddComm α] : IsLeftAddCancel α where
  of_add_left {k a b} h := by
    rw [add_comm k, add_comm k] at h
    exact of_add_right h
public instance (priority := 500) [Add α] [IsLeftAddCancel α] [IsAddComm α] : IsRightAddCancel α where
  of_add_right {k a b} h := by
    rw [add_comm _ k, add_comm _ k] at h
    exact of_add_left h

public instance (priority := 500) [Mul α] [Zero α] [IsRightCancel₀ α] [IsComm α] : IsLeftCancel₀ α where
  of_mul_left₀ {k a b} k_ne_zero h := by
    rw [mul_comm k, mul_comm k] at h
    exact of_mul_right₀ k_ne_zero h
public instance (priority := 500) [Mul α] [Zero α] [IsLeftCancel₀ α] [IsComm α] : IsRightCancel₀ α where
  of_mul_right₀ {k a b} k_ne_zero h := by
    rw [mul_comm _ k, mul_comm _ k] at h
    exact of_mul_left₀ k_ne_zero h

end Property

section Hom

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
@[expose] public protected def MulEquiv.id (α: Type*) [Mul α] : α ≃*ₙ α := {
  Equiv.id _, MulHom.id _ with
}

@[expose] public def MulHom.comp (f: β →*ₙ γ) (g: α →*ₙ β) : α →*ₙ γ where
  toFun := f ∘ g
  map_mul a b := by dsimp only [Function.comp_apply]; rw [map_mul, map_mul]
@[expose] public def MulEmbedding.comp (f: β ↪*ₙ γ) (g: α ↪*ₙ β) : α ↪*ₙ γ := {
  f.toEmbedding.comp g.toEmbedding, f.toMulHom.comp g.toMulHom with
}
@[expose] public def MulEquiv.comp (f: β ≃*ₙ γ) (g: α ≃*ₙ β) : α ≃*ₙ γ := {
  f.toEquiv.comp g.toEquiv, f.toMulHom.comp g.toMulHom with
}
@[expose] public def MulEmbedding.trans (f: α ↪*ₙ β) (g: β ↪*ₙ γ) : α ↪*ₙ γ := comp g f
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
@[expose] public protected def AddEquiv.id (α: Type*) [Add α] : α ≃+ₙ α := {
  Equiv.id _, AddHom.id _ with
}

@[expose] public def AddHom.comp (f: β →+ₙ γ) (g: α →+ₙ β) : α →+ₙ γ where
  toFun := f ∘ g
  map_add a b := by dsimp only [Function.comp_apply]; rw [map_add, map_add]
@[expose] public def AddEmbedding.comp (f: β ↪+ₙ γ) (g: α ↪+ₙ β) : α ↪+ₙ γ := {
  f.toEmbedding.comp g.toEmbedding, f.toAddHom.comp g.toAddHom with
}
@[expose] public def AddEquiv.comp (f: β ≃+ₙ γ) (g: α ≃+ₙ β) : α ≃+ₙ γ := {
  f.toEquiv.comp g.toEquiv, f.toAddHom.comp g.toAddHom with
}
@[expose] public def AddEmbedding.trans (f: α ↪+ₙ β) (g: β ↪+ₙ γ) : α ↪+ₙ γ := comp g f
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

end Hom

section Basic

public instance [Mul α] [IsSemigroup α] : IsAddSemigroup (AddOfMul α) where
  add_assoc := mul_assoc (α := α)
public instance [Add α] [IsAddSemigroup α] : IsSemigroup (MulOfAdd α) where
  mul_assoc := add_assoc (α := α)
public instance [Mul α] [IsComm α] : IsAddComm (AddOfMul α) where
  add_comm a b := mul_comm (α := α) a.get b.get
public instance [Add α] [IsAddComm α] : IsComm (MulOfAdd α) where
  mul_comm a b := add_comm (α := α) a.get b.get
public instance [Mul α] [IsLeftCancel α] : IsLeftAddCancel (AddOfMul α) where
  of_add_left := of_mul_left (α := α)
public instance [Add α] [IsLeftAddCancel α] : IsLeftCancel (MulOfAdd α) where
  of_mul_left := of_add_left (α := α)
public instance [Mul α] [IsRightCancel α] : IsRightAddCancel (AddOfMul α) where
  of_add_right := of_mul_right (α := α)
public instance [Add α] [IsRightAddCancel α] : IsRightCancel (MulOfAdd α) where
  of_mul_right := of_add_right (α := α)

public instance [Mul α] [IsSemigroup α] : IsSemigroup αᵐᵒᵖ where
  mul_assoc _ _ _ := by ext; dsimp; rw [mul_assoc]
public instance [Add α] [IsAddSemigroup α] : IsAddSemigroup αᵃᵒᵖ where
  add_assoc _ _ _ := by ext; dsimp; rw [add_assoc]
public instance [Mul α] [IsComm α] : IsComm αᵐᵒᵖ where
  mul_comm _ _ := by ext; dsimp; rw [mul_comm]
public instance [Add α] [IsAddComm α] : IsAddComm αᵃᵒᵖ where
  add_comm _ _ := by ext; dsimp; rw [add_comm]
public instance [Mul α] [IsRightCancel α] : IsLeftCancel (αᵐᵒᵖ) where
  of_mul_left := of_mul_right (α := α)
public instance [Add α] [IsRightAddCancel α] : IsLeftAddCancel (αᵃᵒᵖ) where
  of_add_left := of_add_right (α := α)
public instance [Mul α] [IsLeftCancel α] : IsRightCancel (αᵐᵒᵖ) where
  of_mul_right := of_mul_left (α := α)
public instance [Add α] [IsLeftAddCancel α] : IsRightAddCancel (αᵃᵒᵖ) where
  of_add_right := of_add_left (α := α)

public instance : IsSemigroup ℕ where
  mul_assoc := Nat.mul_assoc
public instance : IsSemigroup ℤ where
  mul_assoc := Int.mul_assoc
public instance : IsAddSemigroup ℕ where
  add_assoc := Nat.add_assoc
public instance : IsAddSemigroup ℤ where
  add_assoc := Int.add_assoc


public instance : IsComm ℕ where
  mul_comm := Nat.mul_comm
public instance : IsComm ℤ where
  mul_comm := Int.mul_comm
public instance : IsAddComm ℕ where
  add_comm := Nat.add_comm
public instance : IsAddComm ℤ where
  add_comm := Int.add_comm

public instance : IsLeftCancel₀ ℕ where
  of_mul_left₀ h := Nat.mul_left_cancel (Nat.pos_of_ne_zero h)
public instance : IsRightCancel₀ ℕ := inferInstance
public instance : IsLeftCancel₀ ℤ where
  of_mul_left₀ h := (Int.mul_eq_mul_left_iff h).mp
public instance : IsRightCancel₀ ℤ := inferInstance

public instance : IsLeftAddCancel ℕ where
  of_add_left := Nat.add_left_cancel
public instance : IsRightAddCancel ℕ := inferInstance
public instance : IsLeftAddCancel ℤ where
  of_add_left := Int.add_left_cancel
public instance : IsRightCancel₀ ℤ := inferInstance

end Basic

section Theorems

public instance [Mul α] (a: α) : IsCommAt a a where
  mul_comm := rfl
public instance [Add α] (a: α) : IsAddCommAt a a where
  add_comm := rfl
public instance [Mul α] (a b: α) [IsCommAt a b] : IsAddCommAt (AddOfMul.mk a) (AddOfMul.mk b) where
  add_comm := mul_comm a b
public instance [Add α] (a b: α) [IsAddCommAt a b] : IsCommAt (MulOfAdd.mk a) (MulOfAdd.mk b) where
  mul_comm := add_comm a b

end Theorems
