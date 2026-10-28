module

public import Math.Data.Hom.Defs
import Math.Tactic.Basic

public structure Embedding (α β: Sort*) extends Hom α β where
  injective: Function.Injective toFun

infixr:50 " ↪ " => Embedding

public class EmbeddingLike (F: Sort*) (α β: outParam Sort*) extends Funlike F α β where
  coeInjective (f: F): Function.Injective f := by intro f; apply f.injective

@[coe, expose] public def Embedding.coe [EmbeddingLike F α β] (f: F) : α ↪ β where
  toFun := f
  injective := EmbeddingLike.coeInjective _

public instance [EmbeddingLike F α β] : CoeOut F (α ↪ β) where
  coe := Embedding.coe

namespace Embedding

public instance : EmbeddingLike (α ↪ β) α β where

@[expose] public protected def id (α: Sort*) : α ↪ α where
  toFun := id
  injective _ _ := id

variable {α β γ: Sort*}

@[ext] public theorem ext (f g: α ↪ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h
public theorem inj (f: α ↪ β) : Function.Injective f := f.injective

@[simp] public theorem apply_id : Embedding.id α x = x := rfl

@[expose] public protected def comp (f: β ↪ γ) (g: α ↪ β) : α ↪ γ where
  toFun := f ∘ g
  injective := Function.Injective.comp f.inj g.inj
@[expose] public protected def trans (f: α ↪ β) (g: β ↪ γ) : α ↪ γ := g.comp f

@[simp] public theorem apply_comp (f: β ↪ γ) (g: α ↪ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪ β) (g: β ↪ γ) (x: α) : f.trans g x = g (f x) := rfl
