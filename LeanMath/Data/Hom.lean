import LeanMath.Logic.Funlike

structure Hom (α β: Sort*) where
  toFun : α → β

instance (priority := 10000) : FunLike (Hom α β) α β where
