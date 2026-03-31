import LeanMath.Data.Ordinal.Defs
import LeanMath.Data.Set.Finite
import LeanMath.Data.Bijection.Basic
import LeanMath.Data.Fintype.Algebra.Monoid

namespace Ordinal

private def well_order_finite_iso [LEM] (r: Fin n -> Fin n -> Prop) [Relation.IsWellOrder r] : Nonempty (r ≃r (· < ·: Fin n -> Fin n -> Prop)) := by
  induction n with
  | zero =>
    refine ⟨?_⟩
    exact {
      toEquiv := Equiv.empty
      map_rel {a} := elim_empty a
    }
  | succ n ih =>
    have hx : ∃x: Fin (n + 1), True := ⟨0, True.intro⟩
    have ⟨i, ⟨ht, hi⟩, hunique⟩ := Relation.exists_unique_min r hx; clear ht hunique

    replace hi : ∀b, ¬r b i := fun b hb => hi b hb True.intro
    let fi: Fin n ↪ Fin (n + 1) := Embedding.option_some.trans (Equiv.fin_erase i).symm.toEmbedding
    have ⟨eqv⟩ := ih (pullback_rel r fi)
    refine ⟨?_⟩
    apply RelEquiv.trans (pullback_rel_eqv r (
      (Equiv.option_congr eqv.symm.toEquiv).trans
      (Equiv.fin_erase i).symm)
    ).symm

    exact {
      toEquiv := (Equiv.fin_erase 0).symm
      map_rel {a b} := by
        cases a <;> cases b <;> simp [pullback_rel]
        · apply Relation.irrefl
        · rename_i a
          rcases Relation.trichotomous r i (if ↑(eqv.symm a) < i.val then (eqv.symm a).castSucc else (eqv.symm a).succ) with h | h | h
          · assumption
          · split at h <;> rename_i g
            rw [h] at g
            nomatch Nat.lt_irrefl _ g
            rw [h] at g
            nomatch g (Nat.lt_succ_self _)
          · nomatch hi _ h
        · rename_i b
          intro h
          exact hi _ h
        · rename_i a b
          have := map_rel eqv.symm (a := a) (b := b)
          symm; simpa [pullback_rel, fi] using this
    }

def finite {α: Type*} [LEM] [hfinite: Finite α] (r: α -> α -> Prop)
  [Relation.IsTrans r]
  [Relation.IsTrichotomous r (· = ·)]
  [Relation.IsIrrefl r] : ∃n: ℕ, type r = n := by
  have ⟨card, ⟨bij⟩⟩ := Finite.finBij α
  have eqv := Equiv.ofBij bij
  have reqv := pullback_rel_eqv r eqv
  exists card
  have ⟨_⟩ := well_order_finite_iso (pullback_rel r eqv)
  apply sound
  apply reqv.symm.trans
  apply RelEquiv.trans _ (ulift_rel_eqv_rel _).symm
  assumption

end Ordinal
