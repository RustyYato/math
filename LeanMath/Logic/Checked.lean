import LeanMath.Tactic.TypeStar

class CheckedInv (α: Type*) (P: α -> Prop) where
  protected checked_inv (a: α) (p: P a) : α

class CheckedDiv (α: Type*) (P: α -> Prop) where
  protected checked_div (a b: α) (p: P b) : α

class CheckedZPow (α: Type*) (P: α -> Prop) where
  protected checked_div (a: α) (n: ℤ) (p: 0 ≤ n ∨ P a) : α
