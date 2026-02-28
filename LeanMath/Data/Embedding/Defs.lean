import LeanMath.Logic.Funlike

structure Embedding (α β: Sort*) where
  toFun: α -> β
  inj: Function.Injective toFun

infixr:25 " ↪ " => Embedding

namespace Embedding

instance : FunLike (α ↪ β) α β where

protected def id (α: Sort*) : α ↪ α where
  toFun := id
  inj _ _ := id

def comp (f: β ↪ γ) (g: α ↪ β) : α ↪ γ where
  toFun := f ∘ g
  inj _ _ h := g.inj (f.inj h)

abbrev trans (f: α ↪ β) (g: β ↪ γ) : α ↪ γ := g.comp f

@[simp] def apply_id (α: Sort*) (x: α) : Embedding.id α x = x := rfl
@[simp] def apply_comp (f: β ↪ γ) (g: α ↪ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_trans (f: β ↪ γ) (g: α ↪ β) (x: α) : (g.trans f) x = f (g x) := rfl

end Embedding
