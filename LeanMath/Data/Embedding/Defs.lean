import LeanMath.Logic.Funlike

structure Embedding (α β: Sort*) where
  toFun: α -> β
  inj: Function.Injective toFun

infixr:25 " ↪ " => Embedding

class EmbeddingLike (F: Sort*) (α β: outParam Sort*) where
  protected coeEmbedding : F -> α ↪ β := by intro f; exact f.toEmbedding
  protected coeInj : Function.Injective coeEmbedding := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply EmbeddingLike.coeInj
      assumption

--- This is not the interface for ops, just ensures that
--- all ops are implemented
set_option checkBinderAnnotations false in
class EmbeddingOpsCheck (C: Sort u -> Sort u) (F: ∀α β (cα: C α) (cβ: C β), Sort v)
  [∀α β [cα: C α] [cβ: C β], EmbeddingLike (F α β cα cβ) α β]
  where
  protected comp {α β γ: Sort u} [cα: C α] [cβ: C β] [cγ: C γ] : F β γ cβ cγ -> F α β cα cβ -> F α γ cα cγ
  protected trans {α β γ: Sort u} [cα: C α] [cβ: C β] [cγ: C γ] : F α β cα cβ -> F β γ cβ cγ -> F α γ cα cγ
  protected refl (α: Sort u) [cα: C α] : F α α cα cα

instance {F α β: Sort*} [EmbeddingLike F α β] : FunLike F α β where
  coeFun f := (EmbeddingLike.coeEmbedding (F := F) f).toFun
  coeInj := by
    intro a b h
    suffices EmbeddingLike.coeEmbedding a = EmbeddingLike.coeEmbedding b by
      exact EmbeddingLike.coeInj this
    dsimp at h
    revert h;
    generalize EmbeddingLike.coeEmbedding a = a
    generalize EmbeddingLike.coeEmbedding b = b
    intro h
    cases a; cases b; congr

namespace Embedding

instance : FunLike (α ↪ β) α β where

protected def id (α: Sort*) : α ↪ α where
  toFun := id
  inj _ _ := id

def comp (f: β ↪ γ) (g: α ↪ β) : α ↪ γ where
  toFun := f ∘ g
  inj _ _ h := g.inj (f.inj h)

abbrev trans (f: α ↪ β) (g: β ↪ γ) : α ↪ γ := g.comp f

@[simp] def apply_toFun (f: α ↪ β) (x: α) : f.toFun x = f x := rfl

@[simp] def apply_id (α: Sort*) (x: α) : Embedding.id α x = x := rfl
@[simp] def apply_comp (f: β ↪ γ) (g: α ↪ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_trans (f: β ↪ γ) (g: α ↪ β) (x: α) : (g.trans f) x = f (g x) := rfl

end Embedding

def inj [EmbeddingLike F α β] (f: F) : Function.Injective f := by
  intro a b h
  have : EmbeddingLike.coeEmbedding f a = EmbeddingLike.coeEmbedding f b := h
  exact Embedding.inj _ this
