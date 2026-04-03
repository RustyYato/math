import LeanMath.Algebra.Module.Basis
import LeanMath.Algebra.Ring.Module.Set
import LeanMath.Data.LinearCombo.AddGroup
import LeanMath.Algebra.Field.Defs
import LeanMath.Order.Zorn

namespace BasisExists

section

variable (F V: Type*) [FieldOps F] [IsDivisionRing F]
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

variable {F V: Type*} [FieldOps F] [IsDivisionRing F]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul F V] [IsModule F V]

private def LinearCombo.iff_eval_zero
  {U: Set V} :
  (∀lc: LinearCombo F U, Submodule.eval F lc = 0 -> lc = 0) ↔
  Submodule.IsLinindep F U := by
  apply Iff.intro
  · intro ih a b h
    have := ih _ (by
      have := sub_eq_zero_of_eq _ _ h
      rw [←map_sub] at this
      exact this)
    exact (sub_eq_zero _ _).mpr this
  · intro ih lc h
    apply @ih lc 0
    rwa [map_zero]

protected def Subset.insert (U: Subset F V) (v: V) (hv: v ∉ Submodule.span F U) : Subset F V where
  toSet := insert v U
  linindep := by
    classical
    apply LinearCombo.iff_eval_zero.mp
    intro lc hlc
    have := LinearCombo.filter_add_union F (α := V) (insert v U) {v} U (by ext; simp; rw [Eq.comm]) ?_ lc
    · rw [this] at hlc
      rw [map_add] at hlc
      replace hlc := eq_neg_of_add _ _ hlc
      by_cases hf:LinearCombo.get ⟨v, by simp⟩ lc = 0
      · suffices hv:(LinearCombo.filter F (insert v ↑U) {v}) lc = 0 by
          rw [hv] at hlc
          rw [map_zero, map_zero, ←neg_zero, neg_inj,
            LinearCombo.upcast_eval] at hlc
          replace hlc := LinearCombo.iff_eval_zero.mpr U.linindep _ hlc.symm
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

protected def Subset.sup (U: Set (Subset F V)) [U.IsChain (· ≤ ·)]
  (a b: Subset F V) (ha: a ∈ U) (hb: b ∈ U)
  : Subset F V where
  toSet := a.toSet ∪ b.toSet
  linindep := by
    suffices a.toSet ∪ b.toSet = a.toSet ∨ a.toSet ∪ b.toSet = b.toSet by
      rcases this with h | h
      rw [h]; exact a.linindep
      rw [h]; exact b.linindep
    rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, ha⟩ ⟨_, hb⟩ with h | h
    right; ext v; simp ; apply h
    left; ext v; simp ; apply h

protected def Subset.sup_mem (U: Set (Subset F V)) [U.IsChain (· ≤ ·)]
  (a b: Subset F V) (ha: a ∈ U) (hb: b ∈ U)
  : Subset.sup U a b ha hb ∈ U := by
  suffices Subset.sup U a b ha hb = a ∨ Subset.sup U a b ha hb = b by
    rcases this with h | h
    rw [h]; assumption
    rw [h]; assumption
  rcases Relation.total (U.Induced (· ≤ ·)) ⟨_, ha⟩ ⟨_, hb⟩ with h | h
  right; apply SetLike.ext; intro v; simp [show v ∈ Subset.sup U a b ha hb ↔ v ∈ a ∨ v ∈ b from Iff.rfl] ; apply h
  left; apply SetLike.ext; intro v; simp [show v ∈ Subset.sup U a b ha hb ↔ v ∈ a ∨ v ∈ b from Iff.rfl] ; apply h

protected def Subset.sSup (U: Set (Subset F V))
  [U.IsChain (· ≤ ·)] : Subset F V where
  toSet := (⋃ (U.image toSet))
  linindep := by
    classical
    apply LinearCombo.iff_eval_zero.mp
    intro lc hlc
    by_cases hU:U = ⊥
    · subst U
      clear hlc
      induction lc with
      | ι a => nomatch a
      | zero => rfl
      | add a b iha ihb => rw [iha, ihb, add_zero]
    have : _ ↔ U = ⊥ := Set.not_nonempty (a := U)
    rw [←Classical.not_iff, Iff.comm, Classical.not_iff] at this
    rw [this] at hU; clear this
    obtain ⟨elements, nodup, rfl, nontrivial⟩ := LinearCombo.exists_nodup_elements lc
    have : ∃u ∈ U, ∀x ∈ elements, x.fst.val ∈ u := by
      clear nodup nontrivial hlc
      induction elements with
      | nil =>
        have ⟨u, hu⟩ := hU
        exact ⟨u, hu, nofun⟩
      | cons a as ih =>
        obtain ⟨u, hu, ih⟩ := ih
        obtain ⟨⟨v, hv⟩, r⟩ := a
        obtain ⟨_, ⟨u', hu', rfl⟩, hv⟩ := hv
        refine ⟨Subset.sup U u u' hu hu', ?_, ?_⟩
        apply Subset.sup_mem
        intro x hx
        simp at hx; rcases hx with rfl | hx
        right; assumption
        left; apply ih
        assumption
    obtain ⟨u, hu, mem⟩ := this
    rw [LinearCombo.filter_eval_from_basis_mem F _ _ _ mem] at hlc
    rw [←map_zero (Submodule.eval F)] at hlc
    replace hlc := u.linindep hlc
    rw [←map_zero (LinearCombo.upcast F u.toSet (⋃ U.image Subset.toSet) (by
      intro x hx; simp; refine ⟨u, ?_, ?_⟩
      exists u
      assumption)), ←hlc]
    clear hlc; clear hlc nontrivial nodup
    induction elements with
    | nil => simp [map_zero]
    | cons x xs ih =>
      simp [map_add, LinearCombo.filter_ι]
      rw [dif_pos (by
        apply mem
        simp)]
      congr 1
      symm; apply LinearCombo.upcast_ι
      apply ih
      intro y hy
      apply mem
      simp [hy]

end

variable
  (F V: Type*) [FieldOps F] [IsDivisionRing F]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul F V] [IsModule F V]

def exists_basis : ∃U: Set V, Submodule.IsBasis F U := by
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

variable
  (F V: Type*) [FieldOps F] [IsDivisionRing F]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul F V] [IsModule F V]

noncomputable def Submodule.basis : Set V := Classical.choose (BasisExists.exists_basis F V)
def Submodule.IsBasis.basis : Submodule.IsBasis F (Submodule.basis F V) := Classical.choose_spec (BasisExists.exists_basis F V)
