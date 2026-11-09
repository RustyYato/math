module

import Math.Order.Zorn
import Math.Logic.Nontrivial

public import Math.Order.Relation.Defs

namespace Math

@[ext]
structure Relation (α: Type*) where
  toRel : α -> α -> Prop

def Relation.defined (r: Relation α) : Set α where
  Mem x := ∃y, r.toRel x y ∨ r.toRel y x

structure Relation.IsInitialSegment (a b: Relation α) : Prop where
  maps: ∀x y: α, a.toRel x y -> b.toRel x y
  initial: ∀{x y: α}, y ∈ a.defined -> b.toRel x y -> a.toRel x y

theorem Relation.IsInitialSegment.map_defines
  {x: α} {a b: Relation α} (h: Relation.IsInitialSegment a b) (ha: x ∈ a.defined) : x ∈ b.defined := by
  obtain ⟨c, ha⟩ := ha
  rcases ha with ha | ha
  exists c; left; apply h.maps; assumption
  exists c; right; apply h.maps; assumption

instance : LE (Relation α) where
  le := Relation.IsInitialSegment
instance : LT (Relation α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder (Relation α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl _ := {
    maps _ _ := id
    initial _ := id
  }
  htrans h g := {
    maps x y x_lt_y := g.maps _ _ (h.maps _ _ x_lt_y)
    initial := by
      intro x y y_def crel
      have := h.map_defines y_def
      have brel := g.initial (h.map_defines y_def) crel
      exact h.initial y_def brel
  }
  antisymm a b h g := by
    ext x y; apply Iff.intro
    apply h.maps; apply g.maps

structure IsSubWellOrdering (r: Relation α) : Prop where
  wf: IsWelFounded r.toRel
  trans: IsTrans r.toRel
  connected: r.defined.IsChain r.toRel

def Relation.sub_well_orderings (α: Type*) : Set (Relation α) where
  Mem := IsSubWellOrdering

def Relation.insert (r: Relation α) (x: α) : Relation α where
  toRel a b := r.toRel a b ∨ a ∈ r.defined ∧ b = x

theorem Relation.transfer
  (C: Set (Relation α))
  (C_chain: C.IsChain (· ≤ ·))
  {a b: Relation α}
  (ha: a ∈ C) (hb: b ∈ C)
  {x y: α} (h: a.toRel x y) (g: y ∈ b.defined)
  : b.toRel x y := by
  rcases C_chain.connected ⟨a, ha⟩ ⟨b, hb⟩ with le | h | le
  · apply le.maps
    assumption
  · cases h; assumption
  · apply le.initial _ h
    dsimp; assumption

theorem Relation.insert_spec
  {r: Relation α} {x: α}
  (h: r ∈ Relation.sub_well_orderings α)
  (hx: x ∉ r.defined)
  : Relation.insert r x ∈ Relation.sub_well_orderings α where
  wf := sorry
  trans := sorry
  connected := sorry

def Relation.union (C: Set (Relation α)) : Relation α where
  toRel a b := ∃r ∈ C, r.toRel a b

theorem Relation.union_spec
  (C: Set (Relation α))
  (C_sub: C ⊆ Relation.sub_well_orderings α)
  (C_chain: C.IsChain (· ≤ ·))
  : Relation.union C ∈ Relation.sub_well_orderings α where
  wf := sorry
  trans := sorry
  connected := sorry

inductive TrivialRel (x y: α) (h: x ≠ y) : α -> α -> Prop where
| intro : TrivialRel x y h x y

instance : IsTrans (TrivialRel x y x_ne_y) where
  htrans h g := by cases h; cases g; contradiction
instance : IsWelFounded (TrivialRel x y x_ne_y) where
  wf := by
    apply WellFounded.intro
    intro a; apply Acc.intro
    intro b h; cases h
    apply Acc.intro
    intro c h; cases h
    contradiction

def Relation.trivial {x y: α} (h: x ≠ y) : Relation α where
  toRel := TrivialRel x y h

theorem Relation.trivial_spec {x y: α} (h: x ≠ y) : Relation.trivial h ∈ Relation.sub_well_orderings α where
  trans := inferInstanceAs (IsTrans (TrivialRel _ _ h))
  wf := inferInstanceAs (IsWelFounded (TrivialRel _ _ h))
  connected := {
    connected := by
      intro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨_, ha⟩ := ha
      obtain ⟨_, hb⟩ := hb
      rcases ha with ha | ha <;> cases ha
      <;> rcases hb with hb | hb <;> cases hb
      all_goals dsimp [Set.Induced, trivial]
      right; left; rfl
      left; apply TrivialRel.intro
      right; right; apply TrivialRel.intro
      right; left; rfl
  }

public theorem exists_well_ordering (α: Type*) : ∃r: α -> α -> Prop, IsWellOrder r := by
  by_cases h:Subsingleton α
  · exact ⟨fun _ _ => False, {
      htrans := nofun
      wf := by
        apply WellFounded.intro
        intro x; apply Acc.intro
        nofun
      connected a b := by
        right; left; apply Subsingleton.allEq
    }⟩
  have ⟨rel, wo, maximal⟩ := Zorn.partialorder_in (Relation.sub_well_orderings α) ?_
  · refine ⟨rel.toRel, ?_⟩
    refine {
      htrans := wo.trans.htrans
      wf := wo.wf.wf
      connected := ?_
    }
    suffices def_eq_top:rel.defined = ⊤ by
      have := wo.connected
      rw [def_eq_top] at this
      intro a b
      rcases this.connected ⟨a, True.intro⟩ ⟨b, True.intro⟩ with h | h | h
      left; assumption
      right; left; cases h; rfl
      right; right; assumption
    ext x; simp; apply Classical.byContradiction
    intro x_not_defined
    by_cases hrel:rel.defined.Nonempty
    obtain ⟨a, ha⟩ := hrel
    have := maximal (rel.insert x) ?insert_well_order ?sub_insert
    have mem : (rel.insert x).toRel a x := by right; trivial
    rw [this] at mem
    apply x_not_defined
    exists a; right; trivial
    apply Relation.insert_spec
    assumption
    assumption
    refine ⟨?_, ?_⟩
    · intro x y; apply Or.inl
    · intro i j hj i_lt_j
      rcases i_lt_j with _ | ⟨_, rfl⟩; assumption
      contradiction
    rw [Set.not_nonempty] at hrel
    classical
    have := Nontrivial.of_not_subsingleton h
    have ⟨y, x_ne_y⟩ := Nontrivial.exists_ne x
    have := maximal _ (Relation.trivial_spec x_ne_y) ?_
    rw [←this] at hrel
    simp at hrel
    apply hrel x
    exists y; left; apply TrivialRel.intro
    refine ⟨?_, ?_⟩
    · intro x y h
      simp at hrel
      nomatch hrel x ⟨y, .inl h⟩
    · intro i j j_defined i_lt_j
      cases i_lt_j
      rw [hrel] at j_defined
      contradiction
  · intro C C_sub C_chain
    exists Relation.union C
    apply And.intro
    exact Relation.union_spec _ C_sub C_chain
    intro r hr
    refine ⟨?_, ?_⟩
    intro x y x_lt_y
    exists r
    intro x y r_defines_y ⟨s, hs, x_lt_y⟩
    apply Relation.transfer <;> assumption

public def well_order (α: Type*) : α -> α -> Prop :=
  Classical.choose (exists_well_ordering α)
public instance : IsWellOrder (well_order α) :=
  Classical.choose_spec (exists_well_ordering α)
