module

public import Math.Order.Defs
public import Math.Data.Set.Defs

namespace Math

@[expose] public def IsInitial (f: α -> β) [LE α] [LE β] : Prop :=
  ∀(a: α) (b: β), b ≤ f a -> b ∈ Set.range f

public structure InitialSeg (α β: Type*) [LE α] [LE β] extends α →o β where
  protected isInitial : IsInitial toFun

infixr:80 " ≼i " => InitialSeg

public instance (α β: Type*) [LE α] [LE β] : Funlike (α ≼i β) α β where
public instance (α β: Type*) [LE α] [LT α] [IsPartialOrder α] [LE β] [LT β] [IsPreorder β] : EmbeddingLike (α ≼i β) α β where
  coeInjective := by
    intro f a b h
    let f' : α →o β := f.toRelHom
    exact EmbeddingLike.coeInjective f' h
