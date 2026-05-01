import LeanMath.Data.Fintype.Defs
import LeanMath.Data.ENat.Defs

namespace ENat

open ENat

def card_eq_fintype_card (α: Sort u) [LEM] [Fintype α] : ENat.card α = Fintype.card α := by
  open UniqueChoice in
  unfold ENat.card
  induction Fintype.finEquiv α with | _ eqv =>
  rw [dif_pos]; congr
  apply Classical.choose_unique_spec_unique
  exact ⟨eqv⟩
  exists Fintype.card α
  exact ⟨eqv⟩

def card_eq_finencodable_card (α: Sort u) [LEM] [FinEncodable α] : ENat.card α = FinEncodable.card α := by
  apply card_eq_fintype_card

def card_eq_inf_of_not_finite (α: Sort u) (h: ¬Finite α) [LEM] : ENat.card α = ∞ := by
  unfold card; rw [dif_neg]
  intro ⟨n, ⟨eqv⟩⟩
  apply h
  exact Finite.ofBij eqv.toBij

end ENat
