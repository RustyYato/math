import LeanMath.Data.Set.Relation

def wf_iff_exists_min [LEM] {r: α -> α -> Prop} : WellFounded r ↔ ∀s: Set α, s.Nonempty -> ∃x ∈ s, ∀y ∈ s, ¬r y x := by
  apply Iff.intro
  · intro wf s ⟨x, hx⟩
    induction x using wf.induction with
    | _ x ih =>
    rcases em (∃y ∈ s, r y x) with ⟨y, memy, hy⟩ | h
    apply ih <;> assumption
    exists x
    apply And.intro hx
    intro y ymem hy
    apply h; exists y
  · intro exists_min
    apply WellFounded.intro
    intro a
    apply LEM.byContradiction
    intro ha
    have ⟨b, hb, h⟩ := exists_min { Mem x := ¬Acc r x } ⟨a, ha⟩
    replace hb : ¬Acc r b := hb
    replace h : ∀x, ¬Acc r x -> ¬r x b := h
    apply hb
    apply Acc.intro
    intro c cb
    apply LEM.byContradiction
    intro hc
    exact h c hc cb
