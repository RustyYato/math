module

meta import Math.Tactic.Basic
public import Math.Logic.LEM

@[expose] public def exists_unique (P: α -> Prop) := ∃a, P a ∧ ∀b, P b -> a = b

variable {α: Sort*} {P: α -> Prop}

public theorem exists_unique.subsingleton (P: α -> Prop) : Subsingleton { a: α // P a ∧ ∀b: α, P b -> a = b } where
  allEq := by
    intro ⟨a, pa, ha⟩ ⟨b, pb, hb⟩; congr
    apply ha
    assumption

public theorem exists_unique.nonempty (h: exists_unique P) : Nonempty { a: α // P a ∧ ∀b: α, P b -> a = b } := by
  obtain ⟨a, p, h⟩ := h
  exact ⟨a, p, h⟩

namespace Classical

public axiom unique_choice [Subsingleton α] : Nonempty α -> α
-- noncomputable opaque uniqueChoice [Subsingleton α] : Nonempty α -> α := choice

public noncomputable def unique_choose (h: exists_unique P) : α :=
  have := exists_unique.subsingleton P
  (unique_choice h.nonempty).val

public theorem unique_choose_spec (h: exists_unique P) : P (unique_choose h) :=
  have := exists_unique.subsingleton P
  (unique_choice h.nonempty).property.left

public theorem unique_choose_unique (h: exists_unique P) : ∀a: α, P a -> unique_choose h = a :=
  have := exists_unique.subsingleton P
  (unique_choice h.nonempty).property.right

#print Classical.axiomOfChoice

public theorem axiomOfUniqueChoice :
  ∀ {α : Sort u} {β : α → Sort v} {r : (x : α) → β x → Prop},
  (∀ (x : α), exists_unique (r x)) →
  exists_unique fun f: ∀x, β x => ∀ (x : α), r x (f x) := by
  intro α β r h
  refine ⟨fun x => ?_, ?_, ?_⟩
  · exact unique_choose (α := β x) (h x)
  · intro x; apply unique_choose_spec
  · intro f g; ext a
    apply unique_choose_unique
    apply g

namespace UniqueChoice

public noncomputable scoped instance (P: Prop) [ExcludedMiddle P] :
  Decidable P := unique_choice (by
    rcases _root_.em P with p | np
    exact ⟨.isTrue p⟩
    exact ⟨.isFalse np⟩)

end UniqueChoice

end Classical
