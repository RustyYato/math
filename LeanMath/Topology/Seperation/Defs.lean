import LeanMath.Topology.Defs

namespace Topology

def Indistinuishable {α: Type*} (t: Topology α) (a b: α) : Prop :=
  ∀U ∈ t.OpenSets, a ∈ U ↔ b ∈ U

def Distinuishable {α: Type*} (t: Topology α) (a b: α) : Prop :=
  ∃U ∈ t.OpenSets, (a ∈ U ∧ b ∉ U) ∨ (a ∉ U ∧ b ∈ U)

def Separated {α: Type*} (t: Topology α) (a b: α) : Prop :=
  (∃U ∈ t.OpenSets, a ∈ U ∧ b ∉ U) ∧ (∃V ∈ t.OpenSets, a ∉ V ∧ b ∈ V)

def SeparatedByNeighborhoods {α: Type*} (t: Topology α) (a b: α) : Prop :=
  (∃U V, U ∈ t.OpenSets ∧ V ∈ t.OpenSets ∧ a ∈ U ∧ b ∈ V ∧ U ∩ V = ⊥)

def indistinuishable_iff_not_distinuishable [LEM] (t: Topology α) : t.Indistinuishable a b ↔ ¬t.Distinuishable a b := by
  apply Iff.intro
  · intro h ⟨U, Uopen, g⟩
    rcases g with ⟨ha, hb⟩ | ⟨ha, hb⟩
    exact hb <| (h U Uopen).mp ha
    exact ha <| (h U Uopen).mpr hb
  · intro h U Uopen
    apply Iff.intro
    intro ha; apply LEM.byContradiction
    intro hb
    apply h; refine ⟨U, Uopen, ?_⟩
    exact .inl ⟨ha, hb⟩
    intro hb; apply LEM.byContradiction
    intro ha
    apply h; refine ⟨U, Uopen, ?_⟩
    exact .inr ⟨ha, hb⟩

def distinuishable_iff_not_indistinuishable [LEM] (t: Topology α) : t.Distinuishable a b ↔ ¬t.Indistinuishable a b := by
  apply Iff.intro
  · intro ⟨U, Uopen, g⟩ h
    rcases g with ⟨ha, hb⟩ | ⟨ha, hb⟩
    exact hb <| (h U Uopen).mp ha
    exact ha <| (h U Uopen).mpr hb
  · intro h
    replace h : ¬∀_, _ := h
    simp only [LEM.not_forall, LEM.iff_iff_and_or_not_and_not,
      not_or, LEM.not_and, LEM.not_not] at h
    obtain ⟨U, Uopen, ha, hb⟩ := h
    refine ⟨U, Uopen, ?_⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb
    any_goals contradiction
    right; apply And.intro <;> assumption
    left; apply And.intro <;> assumption

def IsT₀ {α: Type*} (t: Topology α) : Prop :=
  ∀x y: α, t.Indistinuishable x y -> x = y

def IsT₁ {α: Type*} (t: Topology α) : Prop :=
  ∀x y: α, x ≠ y -> t.Separated x y

def IsT₂ {α: Type*} (t: Topology α) : Prop :=
  ∀x y: α, x ≠ y -> t.SeparatedByNeighborhoods x y

abbrev IsHausdorff {α: Type*} (t: Topology α) : Prop := t.IsT₂

end Topology

namespace TopologicalSpace

def Indistinuishable {α: Type*} [TopologicalSpace α] (a b: α) : Prop :=
  toTopology.Indistinuishable a b

def Distinuishable {α: Type*} [TopologicalSpace α] (a b: α) : Prop :=
  toTopology.Distinuishable a b

def Separated {α: Type*} [TopologicalSpace α] (a b: α) : Prop :=
  toTopology.Separated a b

def SeparatedByNeighborhoods {α: Type*} [TopologicalSpace α] (a b: α) : Prop :=
  toTopology.SeparatedByNeighborhoods a b

class IsT₀ (α: Type*) [TopologicalSpace α] : Prop where
  protected eq_of_indistinuishable : ∀x y: α, Indistinuishable x y -> x = y

class IsT₁ (α: Type*) [TopologicalSpace α] : Prop where
  protected separated_of_ne : ∀x y: α, x ≠ y -> Separated x y

class IsT₂ (α: Type*) [TopologicalSpace α] : Prop where
  protected separated_by_neighborhood_of_ne : ∀x y: α, x ≠ y -> SeparatedByNeighborhoods x y

abbrev IsHausdorff (α: Type*) [TopologicalSpace α] := IsT₂ α

def eq_of_indistinuishable [TopologicalSpace α] [IsT₀ α] : ∀⦃x y: α⦄, Indistinuishable x y -> x = y :=
  IsT₀.eq_of_indistinuishable

def separated_of_ne [TopologicalSpace α] [IsT₁ α] : ∀⦃x y: α⦄, x ≠ y -> Separated x y :=
  IsT₁.separated_of_ne

def separated_by_neighborhood_of_ne [TopologicalSpace α] [IsT₂ α] : ∀⦃x y: α⦄, x ≠ y -> SeparatedByNeighborhoods x y :=
  IsT₂.separated_by_neighborhood_of_ne

instance [ExcludedMiddleEq α] [TopologicalSpace α] [IsT₁ α] : IsT₀ α where
  eq_of_indistinuishable := by
    intro x y h
    apply LEM.byContradiction
    intro g
    have ⟨⟨U, Uopen, hx, hy⟩, V, Vopen, gx, gy⟩ := separated_of_ne g
    have := (h U Uopen).mp hx
    contradiction

instance [TopologicalSpace α] [IsT₂ α] : IsT₁ α where
  separated_of_ne := by
    intro x y h
    have ⟨U, V, Uopen, Vopen, hx, hy, sep⟩ := separated_by_neighborhood_of_ne h
    refine ⟨⟨U, Uopen, ?_, ?_⟩, ⟨V, Vopen, ?_, ?_⟩⟩
    assumption
    intro hy
    have : y ∈ U ∩ V  := by apply And.intro <;> assumption
    simp [sep] at this
    intro hx
    have : x ∈ U ∩ V  := by apply And.intro <;> assumption
    simp [sep] at this
    assumption

end TopologicalSpace
