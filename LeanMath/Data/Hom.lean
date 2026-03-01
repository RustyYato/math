import LeanMath.Tactic.TypeStar

structure Hom (α β: Type*) where
  toFun : α → β
