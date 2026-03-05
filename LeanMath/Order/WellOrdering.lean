import LeanMath.Order.Zorn

private def rel_defined (r: α -> α -> Prop) : Set α where
  Mem x := ∃y, r x y ∨ r y x

private def rel_defined_nonempty (h: (rel_defined r).Nonempty) : ∃a b, r a b := by
  obtain ⟨a, b, h⟩ := h
  rcases h with h | h
  all_goals exact ⟨_, _, h⟩

private def rel_defined_empty (h: (rel_defined r) = ⊥) : ∀a b, ¬r a b := by
  intro a b rab
  have : a ∈ rel_defined r := ⟨_, .inl rab⟩
  rw [h] at this
  contradiction

private structure SubWellOrdering (α: Type*) where
  rel: α -> α -> Prop
  chain: (rel_defined rel).IsChain rel
  trans: Relation.IsTrans rel
  wf: Relation.IsWelFounded rel

namespace SubWellOrdering

inductive small_rel : α -> α -> α -> α -> Prop where
| intro : small_rel a b a b

def small (a b: α) (h: a ≠ b) : SubWellOrdering α where
  rel := small_rel a b
  chain := {
    trichotomous := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      simp [Set.Induced]
      rcases ha with ⟨_, ha⟩
      rcases hb with ⟨_, hb⟩
      rcases ha with ha | ha <;> rcases hb with hb | hb
      all_goals cases ha <;> cases hb
      right; left; rfl
      left; apply small_rel.intro
      right; right; apply small_rel.intro
      right; left; rfl
  }
  trans := {
     trans := by
      intro a b c h g
      cases h
      cases g
      contradiction
  }
  wf := {
    wf := by
      apply WellFounded.intro
      intro x; apply Acc.intro
      intro _ h; cases h
      apply Acc.intro
      intro _ h; cases h
      contradiction
  }

def defined (w: SubWellOrdering α) := rel_defined w.rel

instance (w: SubWellOrdering α) : w.defined.IsChain w.rel := w.chain
instance (w: SubWellOrdering α) : Relation.IsTrans w.rel := w.trans
instance (w: SubWellOrdering α) : Relation.IsWelFounded w.rel := w.wf

structure SubWellOrdering.le (a b: SubWellOrdering α) where
  implies: ∀x y, a.rel x y -> b.rel x y
  -- a greater order can only extend by adding to the end of the ordering
  initial: ∀x y, b.rel x y -> y ∈ a.defined -> a.rel x y

instance : LE (SubWellOrdering α) where
  le := SubWellOrdering.le
instance : LT (SubWellOrdering α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

def of_rel_defined_le (w₀ w₁: SubWellOrdering α) (h: x ∈ w₀.defined) (g: w₀ ≤ w₁) : x ∈ w₁.defined := by
  obtain ⟨y, h⟩ := h
  exists y
  cases h
  left; apply g.implies
  assumption
  right; apply g.implies
  assumption

instance : IsPartialOrder (SubWellOrdering α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl a := {
    implies _ _ := id
    initial := by
      intro x y h g
      assumption
  }
  trans := by
    intro a b c h g
    exact {
      implies := by
        intro x y hxy
        apply g.implies; apply h.implies
        assumption
      initial := by
        intro x a cx ha
        -- have := of_rel_defined_le _ _ ha h
        apply h.initial
        apply g.initial
        assumption
        apply of_rel_defined_le _ _
        assumption
        assumption
        assumption
    }
  antisymm {a b} h g := by
    obtain ⟨rel₀, _, _, _⟩ := a
    obtain ⟨rel₁, _, _, _⟩ := b
    replace h {x y} : rel₀ x y ↔ rel₁ x y := by
      apply Iff.intro
      apply h.implies
      apply g.implies
    clear g
    congr
    ext; apply h

inductive insert_rel (r: α -> α -> Prop) : α -> α -> α -> Prop where
| lt_top (a top: α) (h: a ∈ rel_defined r) : insert_rel r top a top
| lt (top a b) : r a b ->  insert_rel r top a b

def of_rel_defined_insert (h: a ∈ rel_defined (insert_rel r x)) : a = x ∨ a ∈ rel_defined r := by
  obtain ⟨y, h⟩ := h
  rcases h with h | h <;>
  rcases h with h | h
  · right; assumption
  · right; exists y; left; assumption
  · left; rfl
  · right; exists y; right; assumption

def insert (w: SubWellOrdering α) (x: α) (hx: x ∉ w.defined) : SubWellOrdering α where
  rel := insert_rel w.rel x
  chain := {
    trichotomous := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      simp [Set.Induced]
      replace ha := of_rel_defined_insert ha
      replace hb := of_rel_defined_insert hb
      rcases ha with rfl | ha <;>
      rcases hb with rfl | hb
      · right; left; rfl
      · right; right
        apply insert_rel.lt_top
        assumption
      · left
        apply insert_rel.lt_top
        assumption
      · rcases w.chain.trichotomous ⟨a, ha⟩ ⟨b, hb⟩ with h | h | h
        left; apply insert_rel.lt; assumption
        right; left; apply Subtype.mk.inj h
        right; right; apply insert_rel.lt; assumption
  }
  trans := {
    trans {a b c} h g := by
      cases h <;> cases g
      apply insert_rel.lt_top
      assumption
      exfalso; apply hx
      exists c; left; assumption
      apply insert_rel.lt_top
      exists b
      left; assumption
      apply insert_rel.lt
      apply Relation.trans <;>
      assumption
  }
  wf := {
    wf := by
      suffices ih : ∀ (a: α), a ∈ rel_defined w.rel -> Acc (insert_rel w.rel x) a by
        apply WellFounded.intro
        intro a
        apply Acc.intro
        intro b h
        cases h
        apply ih
        assumption
        apply ih
        exists a; left
        assumption
      intro a ha
      induction a using (Relation.wf w.rel).induction with
      | _ a ih =>
      apply Acc.intro
      intro _ h
      cases h
      contradiction
      apply ih
      assumption
      exists a; left; assumption
  }

def le_insert (w: SubWellOrdering α) (x: α) (hx: x ∉ w.defined) : w ≤ w.insert x hx where
  implies := by
    intro x y h
    apply insert_rel.lt
    assumption
  initial x y h g := by
    cases h
    contradiction
    assumption

def of_rel_defined_ssup (U: Set (SubWellOrdering α)) (h: x ∈ rel_defined (fun a b => ∃w ∈ U, w.rel a b)) : ∃w ∈ U, x ∈ rel_defined w.rel := by
  obtain ⟨y, h⟩ := h
  dsimp at h
  rcases h with ⟨w, hw, h⟩ | ⟨w, hw, h⟩
  refine ⟨w, hw, ?_⟩
  exists y; left; assumption
  refine ⟨w, hw, ?_⟩
  exists y; right; assumption

def sSup (U: Set (SubWellOrdering α)) (hU: U.IsChain (· ≤ ·)) : SubWellOrdering α where
  rel a b := ∃w ∈ U, w.rel a b
  chain := {
    trichotomous := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      simp [Set.Induced]
      replace ha := of_rel_defined_ssup _ ha
      replace hb := of_rel_defined_ssup _ hb
      obtain ⟨w₀, hw₀, ha⟩ := ha
      obtain ⟨w₁, hw₁, hb⟩ := hb
      classical
      let w := if w₀ ≤ w₁ then w₁ else w₀
      have h₀ : w₀ ≤ w := by
        simp [w]
        split; assumption
        rfl
      have h₁ : w₁ ≤ w := by
        simp [w]
        split
        rfl
        rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, hw₀⟩ ⟨_, hw₁⟩
        contradiction
        assumption
      have hw : w ∈ U := by simp [w]; split <;> assumption
      replace ha := of_rel_defined_le _ _ ha h₀
      replace hb := of_rel_defined_le _ _ hb h₁
      rcases w.chain.trichotomous ⟨_, ha⟩ ⟨_, hb⟩ with h | h | h
      · left; refine ⟨w, hw, ?_⟩; assumption
      · right; left; exact Subtype.mk.inj h
      · right; right; refine ⟨w, hw, ?_⟩; assumption
  }
  trans := {
    trans := by
      intro a b c ⟨w₀, hw₀, h₀⟩ ⟨w₁, hw₁, h₁⟩
      classical
      let w := if w₀ ≤ w₁ then w₁ else w₀
      have g₀ : w₀ ≤ w := by
        simp [w]
        split; assumption
        rfl
      have g₁ : w₁ ≤ w := by
        simp [w]
        split
        rfl
        rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, hw₀⟩ ⟨_, hw₁⟩
        contradiction
        assumption
      have hw : w ∈ U := by simp [w]; split <;> assumption
      replace h₀ := g₀.implies _ _ h₀
      replace h₁ := g₁.implies _ _ h₁
      refine ⟨_, hw, ?_⟩
      apply Relation.trans
      assumption
      assumption
  }
  wf := {
    wf := by
      apply WellFounded.intro
      intro a
      apply Acc.intro
      intro b ⟨w, hw, h⟩
      have : b ∈ w.defined := ⟨a, .inl h⟩
      clear a h
      induction b using (Relation.wf w.rel).induction with
      | _ b ih =>
      apply Acc.intro
      intro y hy
      obtain ⟨w', hw', h⟩ := hy
      rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, hw'⟩ ⟨_, hw⟩ with g | g
      · apply ih
        apply g.implies
        assumption
        exists b
        left; apply g.implies
        assumption
      · apply ih
        apply g.initial
        assumption
        dsimp
        simp [Set.Induced] at g
        assumption
        exists b
        left
        apply g.initial
        assumption
        dsimp
        simp [Set.Induced] at g
        assumption
  }

end SubWellOrdering

private def exists_well_ordering (α: Type*) : ∃r: α -> α -> Prop, Relation.IsWellOrder r := by
  have ⟨w, hw⟩ := Zorn.partialorder (α := SubWellOrdering α) ?_
  · exists w.rel
    by_cases h:Subsingleton α
    infer_instance
    replace h : ∃a b: α, a ≠ b := by
      apply Classical.byContradiction
      intro g; simp at g
      apply h
      exact ⟨g⟩
    replace h := h
    have defined_eq_top : w.defined = ⊤ := ?_
    have : Relation.IsTrichotomous w.rel (· = ·) := {
      trichotomous := ?_
    }
    infer_instance
    · intro a b
      have := Relation.trichotomous (w.defined.Induced w.rel) (E := (· = ·)) ⟨a, by
        rw [defined_eq_top]; trivial⟩ ⟨b, by
        rw [defined_eq_top]; trivial⟩
      rcases this with h | h | h
      left; assumption
      right; left; exact Subtype.mk.inj h
      right; right; assumption
    · by_cases hw':w.defined.Nonempty
      · ext x; simp
        apply Classical.byContradiction
        intro hx
        apply hx
        rw [←hw _ (SubWellOrdering.le_insert _ x hx)]
        have ⟨a, b, h⟩ := rel_defined_nonempty hw'
        exists a
        right
        apply SubWellOrdering.insert_rel.lt_top
        exists b; left; assumption
      exfalso
      simp at hw'
      replace hw' := rel_defined_empty hw'
      have ⟨a, b, h⟩ := h
      have g := SubWellOrdering.mk.inj (hw (SubWellOrdering.small a b h) ?_)
      have := hw' a b
      rw [←congrFun (congrFun g a) b] at this
      apply this
      apply SubWellOrdering.small_rel.intro
      exact {
        implies := by
          intro x y h
          nomatch hw' _ _ h
        initial := by
          intro x y h
          cases h
          intro ⟨_, h⟩
          rcases h with h | h <;> nomatch hw' _ _ h
      }
  · intro U hU
    exists SubWellOrdering.sSup U hU
    intro u hu
    refine { implies := ?_, initial := ?_ }
    · intro x y g
      exists u
    · intro x y ⟨w, hw, wrel⟩ hy
      rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, hu⟩ ⟨_, hw⟩ with h | h <;> simp [Set.Induced] at h
      · apply h.initial
        assumption
        assumption
      · apply h.implies
        assumption

def well_order (α: Type*) : α -> α -> Prop := Classical.choose (exists_well_ordering α)
instance : Relation.IsWellOrder (well_order α) := Classical.choose_spec (exists_well_ordering α)

attribute [irreducible] well_order
