import LeanMath.Data.Set.Defs
import LeanMath.Logic.Relation.Defs

variable (r: α -> α -> Prop) [Relation.IsWelFounded r] {U: Set α} (h: U.Nonempty)

def Set.exists_min [LEM] : ∃x ∈ U, ∀y ∈ U, ¬r y x := by
  have ⟨a, mem, min⟩ := Relation.exists_min (α := α) (R := r) (P := (· ∈ U)) (by
    simpa [Set.nonempty_iff_exists] using h)
  refine ⟨a, mem, ?_⟩
  intro y hy rya
  exact min y rya hy

open Classical

noncomputable def Set.min : α := choose (Set.exists_min r h)
def Set.min_mem : min r h ∈ U := (choose_spec (Set.exists_min r h)).left
def Set.min_minimal : ∀x ∈ U, ¬r x (min r h) := (choose_spec (Set.exists_min r h)).right
