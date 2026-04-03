import LeanMath.Tactic.TypeStar
import LeanMath.Logic.LEM

class inductive Nontrivial (α: Sort*) : Prop where
| intro (a b: α) (h: a ≠ b)

instance : Nontrivial Bool :=
  .intro true false (by decide)
instance : Nontrivial Nat :=
  .intro 0 1 (by decide)
instance : Nontrivial Int :=
  .intro 0 1 (by decide)

namespace Nontrivial

variable [h: Nontrivial α]

def exists_ne (a: α) [∀x, ExcludedMiddle (a = x)] : ∃b, a ≠ b := by
  rcases h with ⟨x, y, h⟩
  rcases em (a = x)
  exists y; subst a; assumption
  exists x

end Nontrivial
