module

import Math.Tactic.TypeStar
public import Math.Logic.LEM

public class inductive Nontrivial (α: Sort*) : Prop where
| intro (a b: α) (h: a ≠ b)

public instance : Nontrivial Bool :=
  .intro true false (by decide)
public instance : Nontrivial Nat :=
  .intro 0 1 (by decide)
public instance : Nontrivial Int :=
  .intro 0 1 (by decide)

namespace Nontrivial

public theorem exists_ne [h: Nontrivial α] (a: α) [∀x, ExcludedMiddle (a = x)] : ∃b, a ≠ b := by
  rcases h with ⟨x, y, h⟩
  rcases em (a = x)
  exists y; subst a; assumption
  exists x

public theorem of_not_subsingleton [LEM] (h: ¬Subsingleton α) : Nontrivial α := by
  apply LEM.byContradiction
  intro g; apply h; refine ⟨?_⟩
  intro a b
  apply LEM.byContradiction
  intro h; apply g
  refine ⟨a, b, h⟩

end Nontrivial
