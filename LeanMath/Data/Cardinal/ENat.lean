import LeanMath.Data.Cardinal.Defs
import LeanMath.Data.ENat.Fintype

namespace ENat

def toCard : ℕ∞ ↪ Cardinal where
  toFun
  | (n: ℕ) => .type (Fin n)
  | ∞ => .type ℕ
  inj := by
    intro a b h
    dsimp at h
    cases a <;> cases b <;> dsimp at h
    · have ⟨f⟩ := (Cardinal.exact h)
      congr; exact Equiv.of_fin_eqv f
    · have ⟨f⟩ := (Cardinal.exact h)
      exfalso; apply notFinite ℕ
      apply Finite.ofBij f.toBij
    · have ⟨f⟩ := (Cardinal.exact h)
      exfalso; apply notFinite ℕ
      apply Finite.ofBij f.symm.toBij
    · rfl

@[simp] def toCard_finite (n: ℕ) : toCard n = .type (Fin n) := rfl
@[simp] def toCard_infinite : toCard ∞ = .type ℕ := rfl

noncomputable def ofCard [LEM] (c: Cardinal) : ℕ∞ :=
  c.lift ENat.card <| by
    intro a b ⟨h⟩
    apply ENat.card_eq_of_eqv
    assumption

@[simp] def ofCard_fintype [LEM] [Fintype α] : ofCard (.type α) = Fintype.card α := by
  unfold ofCard
  simp; apply ENat.card_eq_fintype_card

@[simp] def ofCard_infinite [LEM] [Infinite α] : ofCard (.type α) = ∞ := by
  apply ENat.card_eq_inf_of_infinite

def toCard_ofCard [LEM] : Function.LeftInverse ofCard toCard := by
  intro x
  cases x <;> simp [Fintype.card_fin]

def toCard_ulift_ofCard [LEM] : Function.LeftInverse ofCard (Cardinal.ulift ∘ toCard) := by
  intro x
  cases x <;> (
    show ofCard (Cardinal.type _) = _
    simp [Fintype.card_fin, Fintype.card_ulift])

def ofCard_surj [LEM] : Function.Surjective ofCard := by
  intro x
  exists Cardinal.ulift x.toCard
  apply toCard_ulift_ofCard

end ENat
