import LeanMath.Logic.Relation.Defs

/-- like Quot, but has no computational content, however it does have equality -/
structure Relevant {α: Sort u} (r: α -> α -> Prop) [Relation.IsRefl r] [Relation.IsSymm r] [Relation.IsTrans r] : Sort (max 1 u) where
  ofEquiv ::
  equiv: α -> Prop
  spec: ∃x, equiv = r x

namespace Relevant

variable {α: Sort*} {r: α -> α -> Prop} [Relation.IsRefl r] [Relation.IsSymm r] [Relation.IsTrans r]
variable {β: Sort*} {s: β -> β -> Prop} [Relation.IsRefl s] [Relation.IsSymm s] [Relation.IsTrans s]

def mk (r: α -> α -> Prop) [Relation.IsRefl r] [Relation.IsSymm r] [Relation.IsTrans r] (a: α) : Relevant r where
  equiv := r a
  spec := ⟨_, rfl⟩

def ind {motive: Relevant r -> Prop} (mk: ∀x, motive (mk r x)) (x: Relevant r) : motive x := by
  obtain ⟨eqv, x, rfl⟩ := x
  apply mk

def lift (f: α -> β) (h: ∀x y, r x y -> s (f x) (f y)) (x: Relevant r) : Relevant s where
  equiv b := ∃a, s b (f a) ∧ x.equiv a
  spec := by
    obtain ⟨eqv, a, rfl⟩ := x
    dsimp
    exists f a
    ext b
    apply Iff.intro
    · rintro ⟨a', _, g⟩
      apply Relation.trans
      apply h
      assumption
      apply Relation.symm
      assumption
    · intro
      exists a
      apply And.intro
      apply Relation.symm
      assumption
      apply Relation.refl

@[simp] def lift_mk (f: α -> β) (h) (a: α) : lift f h (mk r a) = mk s (f a) := by
  unfold lift mk; dsimp
  congr
  ext b
  apply Iff.intro
  · rintro ⟨a', _, g⟩
    apply Relation.trans
    apply h
    assumption
    apply Relation.symm
    assumption
  · intro
    exists a
    apply And.intro
    apply Relation.symm
    assumption
    apply Relation.refl

def sound {a b: α} : r a b -> mk r a = mk r b := by
  intro h; unfold mk
  congr 1
  ext x
  apply Iff.intro
  · intro g
    apply Relation.trans _ g
    apply Relation.symm
    assumption
  · intro g
    apply Relation.trans _ g
    assumption

def exact {a b: α} : mk r a = mk r b -> r a b := by
  intro h
  rw [ofEquiv.inj h]

def eq_iff {a b: α} : mk r a = mk r b ↔ r a b := by
  apply Iff.intro
  apply exact
  apply sound

end Relevant
