import LeanMath.Algebra.Module.Basis
import LeanMath.Algebra.Ring.Module.Set
import LeanMath.Data.LinearCombo.AddGroup
import LeanMath.Algebra.Field.Defs
import LeanMath.Order.Zorn


namespace BasisExists

section

variable (F V: Type*) [FieldOps F] [IsField F]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul F V] [IsModule F V]

structure Subset where
  toSet: Set V
  linindep: Submodule.IsLinindep F toSet

instance : SetLike (Subset F V) V where

instance : LE (Subset F V) where
  le a b := a.toSet ⊆ b.toSet

instance : LT (Subset F V) where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder (Subset F V) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl _ := Set.sub_refl _
  trans := Set.sub_trans
  antisymm := by
    intro a b h g
    have := Set.sub_antisymm h g
    exact SetLike.coeInj this

end

section

variable {F V: Type*} [FieldOps F] [IsField F]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul F V] [IsModule F V]

protected def Subset.insert (U: Subset F V) (v: V) (hv: v ∉ Submodule.span F U) : Subset F V where
  toSet := insert v U
  linindep := by
    classical
    intro lc hlc
    have := LinearCombo.filter_add_union F (α := V) (insert v U) {v} U (by ext; simp) ?_ lc
    · rw [this] at hlc
      rw [map_add] at hlc
      replace hlc := eq_neg_of_add _ _ hlc
      by_cases hf:LinearCombo.get ⟨v, by simp⟩ lc = 0
      · suffices hv:(LinearCombo.filter F (insert v ↑U) {v}) lc = 0 by
          rw [hv] at hlc
          rw [map_zero, map_zero, ←neg_zero, neg_inj,
            LinearCombo.upcast_eval] at hlc
          replace hlc := U.linindep _ hlc.symm
          rw [this, hlc]; simp [map_zero, add_zero, hv]
        rw [LinearCombo.filter_singleton F v (by simp)]
        rw [hf, map_zero]
      · exfalso
        apply hv
        rw [LinearCombo.upcast_eval, LinearCombo.filter_singleton F v (by simp),
          Submodule.eval_ι] at hlc
        dsimp at hlc
        have smul_congr (f: F) (a₀ a₁: V) : a₀ = a₁ -> f • a₀ = f• a₁ := by intro; congr
        replace hlc := smul_congr (LinearCombo.get ⟨v, _⟩ lc)⁻¹? _ _ hlc
        rw [←mul_smul, inv?_mul_cancel, one_smul] at hlc
        rw [hlc]; apply mem_smul
        apply mem_neg
        rw [LinearCombo.upcast_eval]
        apply Submodule.lincombo_mem_span_of_subset
        apply Submodule.sub_span
    · ext v; simp
      intro rfl
      intro h; apply hv
      apply Submodule.sub_span
      assumption

protected def Subset.sSup (U: Set (Subset F V))
  [U.IsChain (· ≤ ·)] : Subset F V where
  toSet := (⋃ (U.image toSet))
  linindep := by
    intro lc hlc
    sorry

end

def exists_basis
  (F V: Type*) [FieldOps F] [IsField F]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul F V] [IsModule F V]
  : ∃U: Set V, Submodule.IsBasis F U := by
  have ⟨U, hU⟩ := Zorn.partialorder (α := Subset F V) ?_
  · exists U
    refine ⟨?_, U.linindep⟩
    intro v
    apply Classical.byContradiction
    intro hv
    have : v ∈ U.insert v hv := by show v ∈ insert v (U: Set V); simp
    rw [hU (Subset.insert U v hv) ?_] at this
    · apply hv
      apply Submodule.sub_span
      assumption
    · intro w hw; replace hw: w ∈ U := hw
      show w ∈ (insert v U: Set V); simp
      right; assumption
  · intro U _
    exists Subset.sSup U
    intro s hs v hv
    exists s
    simp
    exact ⟨⟨s, hs, rfl⟩, hv⟩

end BasisExists
