import LeanMath.Order.Zorn

namespace WellOrdering

variable {α: Type*} (R: α -> α -> Prop) {r: α -> α -> Prop} (x: α)

def defined (r: α -> α -> Prop) : Set α where
  Mem x := ∃y, r x y ∨ r y x

structure le (r s: α -> α -> Prop) : Prop where
  -- a smaller relation must by contained within the larger one
  implies: ∀{x y}, r x y -> s x y
  -- a greater order can only extend by adding to the end of the ordering
  -- this way the intersection of any two related orderings is always equal
  -- to the smaller one
  initial: ∀{x y}, y ∈ defined r -> s x y -> r x y

scoped instance (priority := 10000) : LE (α -> α -> Prop) where
  le := le
scoped instance (priority := 10000) : LT (α -> α -> Prop) where
  lt a b := a ≤ b ∧ ¬b ≤ a

def defined_of_le (w₀ w₁: α -> α -> Prop) (h: x ∈ defined w₀) (g: w₀ ≤ w₁) : x ∈ defined w₁ := by
  obtain ⟨y, h⟩ := h
  exists y
  cases h
  left; apply g.implies
  assumption
  right; apply g.implies
  assumption

scoped instance : IsPartialOrder (α -> α -> Prop) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl a := {
    implies := id
    initial _ := id
  }
  trans := by
    intro a b c ab bc
    exact {
      implies h := by
        apply bc.implies
        apply ab.implies
        assumption
      initial {x y} hy xy := by
        apply ab.initial
        assumption
        apply bc.initial
        apply defined_of_le
        assumption
        assumption
        assumption
    }
  antisymm {a b} ab ba := by
    ext x y
    apply Iff.intro
    apply ab.implies
    apply ba.implies

class IsSubwellorder : Prop extends Relation.IsTrans R, Relation.IsWelFounded R, (defined R).IsChain R where

inductive small (a b: α) : α -> α -> Prop
| intro : small a b a b

inductive insert : α -> α -> Prop where
| lt_top : a ∈ defined R -> insert a x
| of : R a b -> insert a b

scoped instance (priority := 10000) : Max (α -> α -> Prop) where
  max r s x y := r x y ∨ s x y

scoped instance (priority := 10000) : SupSet (α -> α -> Prop) where
  sSup U x y := ∃r ∈ U, r x y

def left_le_max (r s: α -> α -> Prop) (U: Set (α -> α -> Prop)) [U.IsChain (· ≤ ·)] (hr: r ∈ U) (hs: s ∈ U) : r ≤ r ⊔ s where
  implies := .inl
  initial {x y} hy xy := by
    rcases xy with xy | xy
    assumption
    rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, hr⟩ ⟨_, hs⟩ with h | h
    apply h.initial
    assumption
    assumption
    apply h.implies
    assumption

def right_le_max (r s: α -> α -> Prop) (U: Set (α -> α -> Prop)) [U.IsChain (· ≤ ·)] (hr: r ∈ U) (hs: s ∈ U) : s ≤ r ⊔ s where
  implies := .inr
  initial {x y} hy xy := by
    rcases xy with xy | xy
    rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, hr⟩ ⟨_, hs⟩ with h | h
    apply h.implies
    assumption
    apply h.initial
    assumption
    assumption
    assumption

def max_mem (r s: α -> α -> Prop) (U: Set (α -> α -> Prop)) [U.IsChain (· ≤ ·)] (hr: r ∈ U) (hs: s ∈ U) : r ⊔ s ∈ U := by
  suffices h:r ⊔ s = r ∨ r ⊔ s = s by
    rcases h with h | h <;> rwa [h]
  rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, hr⟩ ⟨_, hs⟩ with h | h
  · right
    ext x y
    apply Iff.intro _ .inr
    intro h
    cases h
    apply h.implies
    assumption
    assumption
  · left
    ext x y
    apply Iff.intro _ .inl
    intro h
    cases h
    assumption
    apply h.implies
    assumption

def of_defined_small {x: α} (h: x ∈ defined (small a b)) : x = a ∨ x = b := by
  obtain ⟨y, hy⟩ := h
  rcases hy with hy | hy <;> cases hy
  left; rfl
  right; rfl

def of_defined_insert {x} (h: a ∈ defined (insert r x)) : a = x ∨ a ∈ defined r := by
  obtain ⟨y, hy⟩ := h
  rcases hy with hy | hy <;> cases hy
  right; assumption
  right; exists y; left; assumption
  left; rfl
  right; exists y; right; assumption

def of_defined_sSup {U: Set (α -> α -> Prop)} (h: a ∈ defined (⨆ U)) : ∃r ∈ U, a ∈ defined r := by
  obtain ⟨y, hy⟩ := h
  rcases hy with ⟨u, hu, hy⟩ | ⟨u, hu, hy⟩
  exact ⟨u, hu, ⟨_, .inl hy⟩⟩
  exact ⟨u, hu, ⟨_, .inr hy⟩⟩

@[implicit_reducible]
protected def IsSubwellorder.small (a b: α) (h: a ≠ b) : IsSubwellorder (small a b) where
  trans := by
    intro x y z h g
    cases h; cases g
    contradiction
  wf := by
    apply WellFounded.intro
    intro x
    apply Acc.intro
    intro y h; cases h
    apply Acc.intro
    intro y h; cases h
    contradiction
  trichotomous := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    replace hx := of_defined_small hx
    replace hy := of_defined_small hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals simp [Set.Induced, small.intro]

@[implicit_reducible]
protected def IsSubwellorder.insert [IsSubwellorder r] (hx: x ∉ defined r) : IsSubwellorder (insert r x) where
  trans {a b c} h g := by
    rcases g with g | g
    apply insert.lt_top
    rcases h with h | h
    assumption
    exists b; left; assumption
    rcases h with h | h
    exfalso; apply hx
    exists c; left; assumption
    apply insert.of
    apply Relation.trans
    assumption
    assumption
  wf := by
    apply WellFounded.intro
    suffices ih:∀y: α, y ∈ defined r -> Acc (insert r x) y by
      intro x
      apply Acc.intro
      intro y h
      cases h
      apply ih
      assumption
      apply ih
      exists x; left; assumption
    intro y hy
    induction y using (Relation.wf r).induction with
    | _ y ih =>
    apply Acc.intro
    intro z hz
    cases hz
    contradiction
    apply ih
    assumption
    exists y; left; assumption
  trichotomous := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [Set.Induced]
    replace ha := of_defined_insert ha
    replace hb := of_defined_insert hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    right; left; rfl
    right; right; apply insert.lt_top
    assumption
    left; apply insert.lt_top
    assumption
    rcases Relation.trichotomous ((defined r).Induced r) ⟨_, ha⟩ ⟨_, hb⟩ with h | h | h
    left; apply insert.of; assumption
    right; left; exact Subtype.mk.inj h
    right; right; apply insert.of; assumption

@[implicit_reducible]
protected def IsSubwellorder.sSup (U: Set (α -> α -> Prop)) [U.IsChain (· ≤ ·)] (hU: ∀r ∈ U, IsSubwellorder r) : IsSubwellorder (⨆ U) where
  trans {a b c} h g := by
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨s, hs, g⟩ := g
    have mem : r ⊔ s ∈ U := by
      apply max_mem
      assumption
      assumption
    have := hU (r ⊔ s) mem
    exists r ⊔ s
    apply And.intro
    assumption
    apply Relation.trans
    left; assumption
    right; assumption
  wf := by
    apply WellFounded.intro
    intro x
    apply Acc.intro
    intro a ⟨r, hr, ha⟩
    have : a ∈ defined r := by exists x; left; assumption
    clear x ha
    have := hU _ hr
    induction a using (Relation.wf r).induction with
    | _ a ih =>
    apply Acc.intro
    intro b ⟨s, hs, ba⟩
    let t := r ⊔ s
    suffices h:r b a by
      apply ih; assumption
      exists a; left; assumption
    apply (left_le_max r s U hr hs).initial
    assumption
    right; assumption
  trichotomous := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [Set.Induced]
    replace ⟨r, hr, ha⟩ := of_defined_sSup ha
    replace ⟨s, hs, hb⟩ := of_defined_sSup hb
    have := max_mem _ _ _ hr hs
    have := hU _ this
    have := Relation.trichotomous ((defined (r ⊔ s)).Induced (r ⊔ s)) ⟨a, by
      apply defined_of_le
      assumption
      apply left_le_max _ _ U
      assumption
      assumption⟩ ⟨b, by
      apply defined_of_le
      assumption
      apply right_le_max _ _ U
      assumption
      assumption⟩
    simp [Set.Induced] at this
    rcases this with h | h | h
    left; exists r ⊔ s
    right; left; assumption
    right; right; exists r ⊔ s

def le_insert (h: x ∉ defined r) : r ≤ insert r x where
  implies {a b} := .of
  initial := by
    intro a b h g
    cases g
    contradiction
    assumption

def le_sSup (U: Set (α -> α -> Prop)) [U.IsChain (· ≤ ·)] (hr: r ∈ U) : r ≤ ⨆ U where
  implies {a b} _ := by exists r
  initial := by
    intro a b h ⟨s, hs, sab⟩
    apply (left_le_max r s U _ _).initial
    assumption
    right; assumption
    assumption
    assumption

def exists_well_ordering (α: Type*) : ∃r: α -> α -> Prop, Relation.IsWellOrder r := by
  by_cases h:Subsingleton α
  · exists fun _ _ => False
    infer_instance
  replace h : ∃a b: α, a ≠ b := by
    apply Classical.byContradiction
    intro g; simp at g
    exact h ⟨g⟩
  have ⟨r, hr, rmax⟩ := Zorn.partialorder_in (α := α -> α -> Prop) (Set.ofMem IsSubwellorder) ?_
  · exists r
    simp at hr
    suffices Relation.IsTrichotomous r (· = ·) from inferInstance
    have rdef : (defined r).Nonempty := by
      apply Classical.byContradiction
      intro g
      have : r = fun _ _ => False := by
        ext x y
        simp; intro xy
        apply g
        exists x; exists y
        left; assumption
      subst r
      obtain ⟨a, b, h⟩ := h
      have : small a b a b := small.intro
      rw [rmax (small a b) (IsSubwellorder.small a b h) {
        implies := nofun
        initial := nofun
      }] at this
      contradiction
    refine ⟨?_⟩
    have : defined r = ⊤ := by
      ext x; simp
      apply Classical.byContradiction
      intro hx
      have insert_eq := rmax _ (IsSubwellorder.insert _ hx) (le_insert _ hx)
      have ⟨a, ha⟩ := rdef
      have : x ∈ defined (insert r x) := by
        exists a
        right; apply insert.lt_top
        assumption
      rw [insert_eq] at this
      contradiction
    intro a b
    have := Relation.trichotomous ((defined r).Induced r) ⟨a, by
      rw [this]; trivial⟩ ⟨b, by
      rw [this]; trivial⟩
    rcases this with h | h | h
    · left; assumption
    · right; left; exact Subtype.mk.inj h
    · right; right; assumption
  · intro U hU _
    refine ⟨_, IsSubwellorder.sSup U ?_, ?_⟩
    apply hU
    intro r hr
    apply le_sSup
    assumption

end WellOrdering

def well_order (α: Type*) : α -> α -> Prop := Classical.choose (WellOrdering.exists_well_ordering α)
instance : Relation.IsWellOrder (well_order α) := Classical.choose_spec (WellOrdering.exists_well_ordering α)

attribute [irreducible] well_order
