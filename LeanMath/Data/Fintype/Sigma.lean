import LeanMath.Data.Fintype.Choice
import LeanMath.Data.Fintype.Algebra.Monoid
import LeanMath.Data.Nat.Basic

namespace Sigma

private def all (n: ℕ) (card: Fin n -> ℕ) :
  Fin (∑i, card i) ≃ Σi, Fin (card i) :=
  match n with
  | 0 => {
    toFun := nofun
    invFun := nofun
    leftInv := nofun
    rightInv := nofun
  }
  | n + 1 =>
    have allsucc := all n (card ∘ Fin.succ)
    have eqv := (Fin.sum (card 0) (∑i: Fin n, card i.succ)).comp
      <| Equiv.fin_cast (n := ∑i, card i) <| by rw [fin_sum_succ]
    eqv.trans <| {
      toFun
      | .inl x => ⟨0, x⟩
      | .inr x =>
        have ⟨i, x⟩ := allsucc x
        ⟨i.succ, x⟩
      invFun
      | ⟨⟨0, _⟩, x⟩ => .inl x
      | ⟨⟨i + 1, hi⟩, x⟩ => .inr (allsucc.symm ⟨⟨i, Nat.lt_of_succ_lt_succ hi⟩, x⟩)
      leftInv x := by
        obtain ⟨i, x⟩ := x
        cases i using Fin.cases with
        | zero => rfl
        | succ i =>
          dsimp [Fin.succ]
          show Sigma.mk (Fin.mk (Fin.val (allsucc (allsucc.symm ⟨i, x⟩)).fst + 1) _) _ = _
          congr
          rw [Equiv.symm_coe]
          show HEq (allsucc (allsucc.symm ⟨i, x⟩)).snd _
          rw [Equiv.symm_coe]
      rightInv x := by
        rcases x with x | x
        dsimp; rfl
        show Sum.inr (allsucc.symm (allsucc x)) = _
        simp
    }

end Sigma

namespace Fintype

section

private def instSigma' (card: Fin n -> ℕ) : Fintype (Σi, Fin (card i)) where
  card := ∑i, card i
  repr := Trunc.mk {
    bij := (Sigma.all _ card).toBij
    try_decode := .some {
      val := (Sigma.all _ card).symm
      property x := by
        dsimp; rw [Equiv.coe_symm]
    }
  }

private def bijOrEquiv : (α ↭ β) ⊕' (α ≃ β) -> (α ↭ β)
| .inl x => x
| .inr x => x.toBij

variable {ι: Sort*} {α: ι -> Sort*} [ft: Fintype ι] [fα: ∀i, Fintype (α i)]

private def factor
  (rι: (Fin (Fintype.card ι) ↭ ι) ⊕' (Fin (Fintype.card ι) ≃ ι))
  (rα: (∀i, Fin (Fintype.card (α (bijOrEquiv rι i))) ↭ α (bijOrEquiv rι i)) ⊕' (∀i, Fin (Fintype.card (α (bijOrEquiv rι i))) ≃ α (bijOrEquiv rι i)))
: (
    Σ' (rι': Fin (Fintype.card ι) ↭ ι), ∀i, Fin (Fintype.card <| α (rι' i)) ↭ α (rι' i)
  ) ⊕' (
    Σ' (rι': Fin (Fintype.card ι) ≃ ι), ∀i, Fin (Fintype.card <| α (rι' i)) ≃ α (rι' i)
  ) := match rι, rα with
    | .inr rι, .inr rα => .inr ⟨rι, rα⟩
    | .inl rι, .inl rα => .inl ⟨rι, rα⟩
    | .inr rι, .inl rα => .inl ⟨rι.toBij, rα⟩
    | .inl rι, .inr rα => .inl ⟨rι, fun i => (rα i).toBij⟩

private def fin_heq (h: n = m) (x: Fin n) (y: Fin m) (g: x = y.cast h.symm) : HEq x y := by
  subst h; simp [g]

instance : Fintype (Σ'i, α i) :=
  (finBijOrEquiv ι).recOnSubsingleton fun rι =>
  (finTruncChoice (fun i => finBijOrEquiv (α (bijOrEquiv rι i)))).recOnSubsingleton fun rα => by
  have := factor rι (factorBijOrEquiv rα)
  clear rι rα
  match this with
  | .inl ⟨rι, rα⟩ =>
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
  | .inr ⟨rι, rα⟩ =>
    have := @instSigma'
    apply ofEquiv (α := Σi: Fin (card ι), Fin (card (α (rι i))))
    exact {
      toFun a := ⟨rι a.1,  rα _ a.2⟩
      invFun a := ⟨rι.symm a.1,  (rα _).symm (cast (by congr; rw [Equiv.symm_coe rι]) a.2)⟩
      leftInv x := by
        obtain ⟨x, ty⟩ := x
        simp
      rightInv x := by
        obtain ⟨x, ty⟩ := x
        simp
        apply fin_heq
        apply inj (rα (rι.symm (rι x)))
        simp; apply eq_of_heq; apply (cast_heq _ _).trans
        congr; any_goals simp
        apply Function.hfunext
        congr <;> simp
        intro i hi hi'
        rfl
        apply fin_heq
        rfl
        any_goals congr <;> simp
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

variable {ι: Sort*} {α: ι -> Sort*} [ft: Finite ι] [fα: ∀i, Finite (α i)]

instance : Finite (Σ'i, α i) := by
  have ⟨ft⟩ := ft
  induction ft.finBij with | _ rι =>
  have ⟨fα, rα⟩ := finChoice (fun i => (fα (rι i)).finBij)
  replace ⟨rα⟩ := finChoose rα
  apply ofBij (α := Σi: Fin (Fintype.card ι), Fin (fα i))
  apply Bijection.bij_congr (Bijection.id _) (Bijection.psigma_congr rι rα) _
  apply Equiv.sigma_equiv_psigma.toBij

end

section

variable {ι: Type*} {α: ι -> Type*} [ft: Fintype ι] [fα: ∀i, Fintype (α i)]

instance : Finite (Σi, α i) :=
  ofBij (α := Σ'i, α i) Equiv.sigma_equiv_psigma.symm.toBij

end

end Finite
