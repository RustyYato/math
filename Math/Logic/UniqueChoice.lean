module

meta import Math.Tactic.Basic

public def exists_unique (P: α -> Prop) := ∃a, P a ∧ ∀b, P b -> a = b

variable {α: Type*} {P: α -> Prop}

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

end Classical
