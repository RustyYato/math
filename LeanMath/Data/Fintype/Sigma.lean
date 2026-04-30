import LeanMath.Data.FinEncodable.Sigma
import LeanMath.Data.Fintype.Choice

namespace Fintype

section

variable {ι: Sort*} {α: ι -> Sort*} [ft: Fintype ι] [fα: ∀i, Fintype (α i)]

instance : Fintype (Σ'i, α i) :=
  (truncFinEncodable (inferInstance : Fintype ι)).recOnSubsingleton fun rι =>
  (finTruncChoice (fun i => truncFinEncodable (inferInstance : Fintype (α (rι.bij i))))).recOnSubsingleton fun rα =>
  match rι.try_decode with
  | .none => by
    apply ofBij (α := (Σ'i, α (rι.bij i)))
    exact {
      toFun x := ⟨rι.bij x.1, x.2⟩
      inj' {a b} h := by
        dsimp at h
        obtain ⟨ ⟩ := a
        obtain ⟨ ⟩ := b
        dsimp at h
        have ⟨h₀, h₁⟩ := PSigma.mk.inj h
        cases rι.bij.inj h₀
        cases eq_of_heq h₁
        rfl
      surj' := by
        intro ⟨i, h⟩
        obtain ⟨i, rfl⟩ := rι.bij.surj i
        exists ⟨i, h⟩
    }
  | .some rιinv => by
    apply ofEquiv (α := (Σ'i, α (rι.bij i)))
    exact {
      toFun x := ⟨rι.bij x.1, x.2⟩
      invFun x := ⟨rιinv.val x.1, cast (by
        congr
        obtain ⟨i, h⟩ := x
        dsimp
        clear h
        obtain ⟨i, rfl⟩ := rι.bij.surj i
        rw [rιinv.property]) x.2⟩
      leftInv := by
        intro ⟨i, h⟩
        dsimp; congr
        · obtain ⟨i, rfl⟩ := rι.bij.surj i
          rw [rιinv.property]
        · apply cast_heq
      rightInv := by
        intro ⟨i, h⟩
        dsimp; congr
        rw [rιinv.property]
        apply cast_heq
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
