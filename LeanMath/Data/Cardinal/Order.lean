import LeanMath.Data.Cardinal.Defs
import LeanMath.Data.Ordinal.Defs
import LeanMath.Order.WellOrdering

namespace Ordinal

def card : Ordinal -> Cardinal :=
  lift (fun {α} _ => Cardinal.type α) <| by
    intro _ _ _  _ _ _ h
    apply Cardinal.sound
    exact h.toEquiv

def card_surj : Function.Surjective card := by
  intro x
  cases x with | _ α =>
  exists (Ordinal.type (well_order α))

def IsInitial (o: Ordinal) : Prop := ∀x: Ordinal, o.card = x.card -> o ≤ x

def IsInitial.to_lt [LEM] (a b: Ordinal) (ha: a.IsInitial) (hb: b.IsInitial) : a < b -> a.card < b.card := by
  open Classical in
  intro h
  cases a with | @type α r =>
  cases b with | @type β s =>
  have ⟨f⟩ := h
  dsimp at f
  show Cardinal.type α < Cardinal.type β
  apply And.intro ⟨f.toEmbedding⟩
  intro ⟨g⟩
  replace g := Equiv.antisymm f.toEmbedding g
  have := hb (type r) ?_
  have := not_le_of_lt h
  contradiction
  apply Cardinal.sound
  dsimp; apply Equiv.symm
  assumption

end Ordinal

namespace Cardinal

variable [LEM]

private def exists_ord (c: Cardinal) : ∃o: Ordinal, c = o.card := by
  cases c with | type α =>
  exists Ordinal.type (well_order α)
private noncomputable def to_initial_ord' (c: Cardinal) := Relation.min (· < ·) c.exists_ord
private def to_initial_ord'_spec (c: Cardinal) : c.to_initial_ord'.IsInitial := by
  intro x hx
  have h := Relation.min_spec (· < ·) c.exists_ord
  replace h := h.trans hx
  rw [h]; classical
  apply le_of_not_lt
  intro g
  apply Relation.min_minimal (· < ·) x.card.exists_ord
  assumption
  rfl
noncomputable def to_initial_ord : (· ≤ ·: Cardinal -> Cardinal -> Prop) ↪r (· ≤ ·: Ordinal -> Ordinal -> Prop) where
  toFun := to_initial_ord'
  inj := by
    intro a b h
    have ha := Relation.min_spec (· < ·) a.exists_ord
    have hb := Relation.min_spec (· < ·) b.exists_ord
    rw [ha, hb]
    congr 1
  map_rel := by
    intro a b
    apply flip Iff.intro
    · intro h
      have ⟨α, r, hr, ha⟩ := a.to_initial_ord'.exists_eq_type
      have ⟨β, s, hs, hb⟩ := b.to_initial_ord'.exists_eq_type
      rw [ha, hb] at h
      obtain ⟨h⟩ := h
      dsimp at h
      have ga := Relation.min_spec (· < ·) a.exists_ord
      have gb := Relation.min_spec (· < ·) b.exists_ord
      rw [ga, gb]
      show a.to_initial_ord'.card ≤ b.to_initial_ord'.card
      rw [ha, hb]
      refine ⟨?_⟩
      exact h.toEmbedding
    · intro h
      classical
      apply le_of_not_lt
      intro g
      have := Ordinal.IsInitial.to_lt
        b.to_initial_ord' a.to_initial_ord'
        (to_initial_ord'_spec _)
        (to_initial_ord'_spec _)
        g
      have ga : a = a.to_initial_ord'.card := Relation.min_spec (· < ·) a.exists_ord
      have gb : b = b.to_initial_ord'.card := Relation.min_spec (· < ·) b.exists_ord
      rw [←ga, ←gb] at this
      clear ga gb g
      have := not_le_of_lt this
      contradiction

noncomputable def to_initial_ord_lt : (· < ·: Cardinal -> Cardinal -> Prop) ↪r (· < ·: Ordinal -> Ordinal -> Prop) where
  toEmbedding := to_initial_ord.toEmbedding
  map_rel := by
    open Classical in
    intro a b
    rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, map_rel to_initial_ord, map_rel to_initial_ord]
    rfl

instance : @Relation.IsTotal Cardinal (· ≤ ·) := to_initial_ord.liftTotal
open Classical in
instance : @Relation.IsTrichotomous Cardinal (· < ·) (· = ·) := inferInstance
instance : @Relation.IsWelFounded Cardinal (· < ·) := to_initial_ord_lt.liftWellfounded
open Classical in
instance : IsLinearOrder Cardinal where

instance : @Relation.IsWellOrder Cardinal (· < ·) where
  trichotomous := by
    intro a b; classical
    rcases Relation.total (α := Cardinal) (· ≤ ·) a b with h | h
    all_goals rcases lt_or_eq_of_le h with h | rfl
    left; assumption
    right; left; rfl
    right; right; assumption
    right; left; rfl

noncomputable def succ (c: Cardinal.{u}) : Cardinal.{u} :=
  Set.min (· < ·) (U := Set.Ioi c) <| by
    exists 2 ^ c
    apply Cardinal.lt_two_pow

def lt_succ (c: Cardinal) : c < c.succ := by
  show c.succ ∈ Set.Ioi c
  apply Set.min_mem

def of_lt_succ (c: Cardinal) : ∀{x}, x < c.succ -> x ≤ c := by
  classical
  intro x hx; apply le_of_not_lt
  intro h
  exact Set.min_minimal (· < ·) (U := Set.Ioi c) ⟨_, h⟩ x h hx

def succ_le (c: Cardinal) : ∀{x}, c < x -> c.succ ≤ x := by
  classical
  intro x cx; apply le_of_not_lt
  intro h
  have := not_lt.mpr (of_lt_succ _ h)
  contradiction

def succ_finite (n: ℕ) : succ n = (n + 1: ℕ) := by
  open Classical in
  apply le_antisymm
  · apply succ_le
    rw [natCast_lt_natCast]
    apply Nat.lt_succ_self
  · classical
    apply le_of_not_lt
    intro h
    have ⟨m, hm⟩ := lt_omega_iff_natCast.mp (lt_trans h (natCast_lt_omega (n + 1)))
    rw [hm, natCast_lt_natCast, Nat.lt_succ_iff] at h
    rcases Or.symm (Nat.lt_or_eq_of_le h) with h | h
    subst m
    · have := lt_succ n
      rw [hm] at this
      exact Relation.irrefl this
    · rw [←natCast_lt_natCast, ←hm] at h
      apply not_le_of_lt h
      apply le_of_lt
      apply lt_succ

def omega_ne_succ : ∀{c: Cardinal}, c.succ ≠ ω := by
  intro c
  intro h
  have := lt_succ c
  rw [h] at this
  rw [lt_omega_iff_natCast] at this
  obtain ⟨n, rfl⟩ := this
  rw [succ_finite] at h
  have := natCast_lt_omega (n + 1)
  rw [h] at this
  exact Relation.irrefl this

def succ_lt_succ {a b: Cardinal} : a.succ < b.succ ↔ a < b := by
  classical
  apply Iff.intro
  · intro h
    apply lt_of_lt_of_le _ (of_lt_succ _ h)
    apply lt_succ
  · intro h
    have := succ_le _ h
    apply lt_of_le_of_lt
    exact succ_le _ h
    apply lt_succ

def succ_inj : Function.Injective succ := by
  intro a b eq
  rcases Relation.trichotomous (· < ·) a b with h | h | h
  rw [←succ_lt_succ, eq] at h
  nomatch Relation.irrefl h
  assumption
  rw [←succ_lt_succ, eq] at h
  nomatch Relation.irrefl h

end Cardinal
