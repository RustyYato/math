module

public import Math.Data.Set.Defs
public import Math.Logic.LEM

namespace Math.Set

public protected abbrev Nonempty (s: Set α) : Prop := Nonempty s

public theorem nonempty_spec (s: Set α) : s.Nonempty ↔ ∃a, a ∈ s := by
  apply Iff.intro
  iterate 2
  intro ⟨a, h⟩
  exact ⟨a, h⟩

@[simp] public theorem not_nonempty {a: Set α} : ¬a.Nonempty ↔ a = ⊥ := by
  apply Iff.intro
  intro h; ext x; simp
  intro g; apply h; exists x
  rintro rfl
  intro h
  obtain ⟨x, hx⟩ := h
  contradiction

@[simp] public theorem eq_empty_iff {a: Set α} : a = ⊥ ↔ ∀x, x ∉ a := by
  apply Iff.intro
  intro rfl; nofun
  intro h
  ext a
  simp [h]

@[simp] public theorem ne_empty [LEM] {a: Set α} : a ≠ ⊥ ↔ a.Nonempty := by
  apply LEM.not_iff_not.mp
  apply Iff.trans LEM.not_not
  exact not_nonempty.symm

public theorem exists_elem (s: Set α) [s.Nonempty] : ∃x, x ∈ s := by
  rwa [←nonempty_spec]

public instance (a: α) : Set.Nonempty {a} := by exists a

public instance : Inhabited ({a}: Set α) where
  default := ⟨a, rfl⟩

public instance : Inhabited (insert a x: Set α) where
  default := ⟨a, by simp⟩

public instance {a b: Set α} [h: Nonempty a] : Nonempty (a ∪ b: Set _) := by
    obtain ⟨x, h⟩ := h
    exact ⟨x, by simp [h]⟩

public instance {a b: Set α} [h: Nonempty b] : Nonempty (a ∪ b: Set _) := by
    obtain ⟨x, h⟩ := h
    exact ⟨x, by simp [h]⟩

public instance  [h : Nonempty ι] (f : ι → α) : (range f).Nonempty := by
  obtain ⟨x⟩ := h

  refine ⟨f x, by simp⟩

public instance (s: Set α) (f: α -> β) [s.Nonempty] : (s.image f).Nonempty := by
  have ⟨x, h⟩ := exists_elem s
  exists f x; simp
  exists x

public theorem empty_not_nonempty : ¬Set.Nonempty (⊥: Set α) := nofun

macro_rules
| `(tactic|contradiction) => `(tactic|exfalso; apply empty_not_nonempty; assumption)
