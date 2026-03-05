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

def IsInitial.to_lt (a b: Ordinal) (ha: a.IsInitial) (hb: b.IsInitial) : a < b -> a.card < b.card := by
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
    intro a b
    rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, map_rel to_initial_ord, map_rel to_initial_ord]
    rfl

instance : @Relation.IsTotal Cardinal (· ≤ ·) := to_initial_ord.liftTotal
instance : @Relation.IsWelFounded Cardinal (· < ·) := to_initial_ord_lt.liftWellfounded
instance : IsLinearOrder Cardinal where

end Cardinal
