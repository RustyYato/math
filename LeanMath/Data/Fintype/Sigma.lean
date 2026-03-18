import LeanMath.Data.Fintype.Choice
import LeanMath.Data.Fintype.Algebra.Monoid
import LeanMath.Data.Nat.Basic

namespace Sigma

private def all (n: ℕ) (card: Fin n -> ℕ) :
  Fin (∑i, card i) ↭ Σi, Fin (card i) :=
  match n with
  | 0 => {
    toFun := nofun
    inj' := nofun
    surj' := nofun
  }
  | n + 1 =>
    have allsucc := all n (card ∘ Fin.succ)
    have eqv := (Fin.sum (card 0) (∑i: Fin n, card i.succ)).comp
      <| Equiv.fin_cast (n := ∑i, card i) <| by rw [fin_sum_succ]
    eqv.toBij.trans <| {
      toFun
      | .inl x => ⟨0, x⟩
      | .inr x =>
        have ⟨i, x⟩ := allsucc x
        ⟨i.succ, x⟩
      inj' := by
        intro a b h; dsimp at h
        cases a <;> cases b <;> (dsimp at h)
        congr
        replace h := Sigma.mk.inj h
        exact eq_of_heq h.2
        replace h := Sigma.mk.inj h
        have := Fin.succ_ne_zero _ h.1.symm
        contradiction
        replace h := Sigma.mk.inj h
        have := Fin.succ_ne_zero _ h.1
        contradiction
        congr
        rename_i a b
        refine @allsucc.inj _ _ a b ?_
        simp at h
        ext1
        exact h.left
        exact h.right
      surj' := by
        intro ⟨a, b⟩
        cases a using Fin.cases
        exists .inl b
        rename_i a
        have ⟨i, hi⟩ := allsucc.surj ⟨a, b⟩
        exists .inr i
        dsimp;
        have ⟨_, _⟩ := Sigma.mk.inj hi
        congr
    }

end Sigma

namespace Fintype

section

private def instSigma' (card: Fin n -> ℕ) : Fintype (Σi, Fin (card i)) where
  card := ∑i, card i
  repr := Trunc.mk {
    bij := Sigma.all _ card
    try_decode := .none
  }

variable {ι: Sort*} {α: ι -> Sort*} [ft: Fintype ι] [fα: ∀i, Fintype (α i)]

instance : Fintype (Σ'i, α i) :=
  (finBij ι).recOnSubsingleton fun rι =>
  (finTruncChoice (fun i => finBij (α (rι i)))).recOnSubsingleton fun rα => by
  have := @instSigma'
  apply ofBij (α := Σi: Fin (card ι), Fin (card (α (rι i))))
  exact {
    toFun a := ⟨rι a.1,  rα _ a.2⟩
    inj' := by
      intro ⟨a₀, a₁⟩ ⟨b₀, b₁⟩ h
      dsimp at h
      have ⟨h₀, h₁⟩ := (PSigma.mk.inj h)
      cases rι.inj h₀
      have := (rα a₀).inj (eq_of_heq h₁)
      congr
    surj' := by
      intro ⟨a, b⟩
      obtain ⟨a, rfl⟩ := rι.surj a
      obtain ⟨b, h⟩ := (rα _).surj b
      exists ⟨a, b⟩
      dsimp; congr
  }

end

section

variable {ι: Type*} {α: ι -> Type*} [ft: Fintype ι] [fα: ∀i, Fintype (α i)]

instance : Fintype (Σi, α i) :=
  ofEquiv (α := Σ'i, α i) Equiv.sigma_equiv_psigma.symm

end

end Fintype

namespace Finite

section

private def instSigma' (card: Fin n -> ℕ) : Fintype (Σi, Fin (card i)) where
  card := ∑i, card i
  repr := Trunc.mk {
    bij := Sigma.all _ card
    try_decode := .none
  }

variable {ι: Sort*} {α: ι -> Sort*} [ft: Finite ι] [fα: ∀i, Finite (α i)]

instance : Finite (Σ'i, α i) := by
  have ⟨ft⟩ := ft
  induction ft.finBij with | _ rι =>
  have ⟨fα, rα⟩ := finChoice (fun i => (fα (rι i)).finBij)
  replace ⟨rα⟩ := finChoose rα
  apply ofBij (α := Σi: Fin (Fintype.card ι), Fin (fα i))
  exact {
    toFun a := ⟨rι a.1,  rα _ a.2⟩
    inj' := by
      intro ⟨a₀, a₁⟩ ⟨b₀, b₁⟩ h
      dsimp at h
      have ⟨h₀, h₁⟩ := (PSigma.mk.inj h)
      cases rι.inj h₀
      have := (rα a₀).inj (eq_of_heq h₁)
      congr
    surj' := by
      intro ⟨a, b⟩
      obtain ⟨a, rfl⟩ := rι.surj a
      obtain ⟨b, h⟩ := (rα _).surj b
      exists ⟨a, b⟩
      dsimp; congr
  }

end

section

variable {ι: Type*} {α: ι -> Type*} [ft: Fintype ι] [fα: ∀i, Fintype (α i)]

instance : Finite (Σi, α i) :=
  ofBij (α := Σ'i, α i) Equiv.sigma_equiv_psigma.symm.toBij

end

end Finite
