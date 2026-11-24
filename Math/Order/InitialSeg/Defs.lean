module

public import Math.Order.Defs
public import Math.Data.Set.Defs

namespace Math

@[expose] public def IsInitial (f: α -> β) (s: β -> β -> Prop) : Prop :=
  ∀(a: α) (b: β), s b (f a) -> b ∈ Set.range f

public structure InitialSeg {α β: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends r →r s where
  protected isInitial : IsInitial toFun s

public abbrev InitialSegLe (α β: Type*) [LE α] [LE β] := @InitialSeg α β (· ≤ ·) (· ≤ ·)

infixr:80 " ≤i " => InitialSegLe

public instance (α β: Type*) [LE α] [LE β] : Funlike (α ≤i β) α β where
public instance (α β: Type*) [LE α] [LT α] [IsPartialOrder α] [LE β] [LT β] [IsPreorder β] : EmbeddingLike (α ≤i β) α β where
  coeInjective := by
    intro f a b h
    let f' : α →o β := f.toRelHom
    exact EmbeddingLike.coeInjective f' h
