
structure Embedding (α β: Sort u) where
  toFun: α -> β
  protected inj: Function.Injective toFun

structure Equiv (α β: Sort u) where
  toFun: α -> β
  invFun: β -> α
  leftInv: Function.LeftInverse toFun invFun
  rightInv: Function.RightInverse toFun invFun

infixr:50 " ↪ " => Embedding

infixr:50 " ≃ " => Equiv

namespace Equiv

def inj (f: α ≃ β) : Function.Injective f.toFun := f.rightInv.injective

def toEmbedding (f: α ≃ β) : α ↪ β where
  toFun := f.toFun
  inj := f.inj

end Equiv


class DFunLike (F: Sort _) (α: outParam (Sort _)) (β: outParam (α -> Sort _)) where
  coeFun (f: F) (a: α) : β a := by intro f; exact f.toFun
  coeInj: Function.Injective coeFun := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply DFunLike.coeInj
      assumption

instance [DFunLike F α β] : CoeFun F (fun _ => ∀x, β x) where
  coe := DFunLike.coeFun

abbrev FunLike (F: Sort _) (α β: Sort _) := DFunLike F α (fun _ => β)

class EmbeddingLike (F: Sort u) (α β: outParam (Sort _)) where
  protected coeEmbedding : F -> α ↪ β := by intro f; exact f.toEmbedding
  protected coeInj : Function.Injective coeEmbedding

class EquivLike (F: Sort u) (α β: outParam (Sort _)) where
  protected coeEquiv : F -> α ≃ β := by intro f; exact f.toEquiv
  protected coeInj : Function.Injective coeEquiv

instance {F α β: Sort _} [EmbeddingLike F α β] : FunLike F α β where
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

instance [EquivLike F α β] : EmbeddingLike F α β where
  coeEmbedding := Equiv.toEmbedding ∘ EquivLike.coeEquiv
  coeInj := sorry

class IsZeroHom (F α β: Type _) [FunLike F α β] [Zero α] [Zero β] where
  protected map_zero (f: F) : f 0 = 0 := by intro f; exact f.map_zero

structure MyEquiv (α β: Sort _) [Zero α] [Zero β] extends α ≃ β where
  map_zero : toFun 0 = 0

variable [Zero α] [Zero β]

instance : EquivLike (MyEquiv α β) α β where
  coeInj := sorry
instance : IsZeroHom (MyEquiv α β) α β where
  map_zero := sorry

def testme [Zero α] [Zero β] [EmbeddingLike F α β] [IsZeroHom F α β] (f: F) : Unit := ()

def MyEquiv.make : MyEquiv α α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl

example : Unit := testme (MyEquiv.make (α := α))
