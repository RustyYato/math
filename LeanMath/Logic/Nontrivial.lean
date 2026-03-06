import LeanMath.Tactic.TypeStar

class inductive Nontrivial (α: Sort*) where
| intro (a b: α) (h: a ≠ b)

instance : Nontrivial Bool :=
  .intro true false (by decide)
instance : Nontrivial Nat :=
  .intro 0 1 (by decide)
instance : Nontrivial Int :=
  .intro 0 1 (by decide)

namespace Nontrivial

variable [h: Nontrivial α]

def exists_ne [DecidableEq α] (a: α) : ∃b, a ≠ b := by
  rcases h with ⟨x, y, h⟩
  by_cases a = x
  exists y; subst a; assumption
  exists x

end Nontrivial
