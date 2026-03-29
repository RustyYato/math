import LeanMath.Data.Set.Defs
import LeanMath.Logic.Relation.Defs

variable (r: α -> α -> Prop) [Relation.IsWelFounded r] {U: Set α} (h: U.Nonempty)

def Set.exists_min [LEM] : ∃x ∈ U, ∀y ∈ U, ¬r y x := by
  have ⟨a, mem, min⟩ := Relation.exists_min (α := α) (R := r) (P := (· ∈ U)) (by
    simpa [Set.nonempty_iff_exists] using h)
  refine ⟨a, mem, ?_⟩
  intro y hy rya
  exact min y rya hy

section

open Classical

noncomputable def Set.arb_min : α := choose (Set.exists_min r h)
def Set.arb_min_mem : arb_min r h ∈ U := (choose_spec (Set.exists_min r h)).left
def Set.arb_min_minimal : ∀x ∈ U, ¬r x (arb_min r h) := (choose_spec (Set.exists_min r h)).right

end

variable [Relation.IsTrichotomous r (· = ·)]

def Set.exists_unique_min [LEM] : existsUnique fun x => x ∈ U ∧ ∀y ∈ U, ¬r y x := by
  have ⟨a, ⟨mem, min⟩, unique⟩ := Relation.exists_unique_min (α := α) (R := r) (P := (· ∈ U)) (by
    simpa [Set.nonempty_iff_exists] using h)
  refine ⟨a, ⟨mem, ?_⟩, ?_⟩
  intro y hy rya
  exact min y rya hy
  intro b ⟨memb, hb⟩
  refine unique b ⟨memb, ?_⟩
  intro x hxb
  intro hx
  apply hb _ hx
  assumption

section

variable [LEM]

noncomputable def Set.min : α := Classical.choose_unique (Set.exists_unique_min r h)
def Set.min_mem : min r h ∈ U := (Classical.choose_unique_spec (Set.exists_unique_min r h)).left
def Set.min_minimal : ∀x ∈ U, ¬r x (min r h) := (Classical.choose_unique_spec (Set.exists_unique_min r h)).right

end
