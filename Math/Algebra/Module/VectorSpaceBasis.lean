module

public import Math.Algebra.Module.Set.Basis.Group
public import Math.Algebra.Field.Defs
import Math.Order.Zorn

namespace Math

section

variable {R V: Type*} [FieldOps R] [IsDivisionRing R]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul R V] [IsModule R V]

theorem insert_linear_independent
  (B: Set V) (v: V) (hB: IsModule.IsLinearIndependent R B) (h: v ∉ Submodule.span R B) :
  IsModule.IsLinearIndependent R (insert v B) := by
  classical
  rw [IsModule.linindep_iff_eq_zero_of_eval_0] at *
  intro lc lc_eval_eq_zero
  let i : (insert v B: Set V) := ⟨v, by simp⟩
  let r := lc.get i
  rw [←add_zero lc, ←neg_add_cancel (LinearCombo.ι R i r),
    ←add_assoc, ←sub_eq_add_neg, map_add, IsModule.eval_ι] at lc_eval_eq_zero
  let lc' := (lc - LinearCombo.ι R i r).filter R B
  rw [
    show
      (IsModule.eval R (insert v B)) (lc - (LinearCombo.ι R i) r) = IsModule.eval R B lc' from ?_
  ] at lc_eval_eq_zero
  replace lc_eval_eq_zero : IsModule.eval R B lc' + r • v = 0 := lc_eval_eq_zero
  by_cases hr:r = 0
  · rw [hr, zero_smul, add_zero] at lc_eval_eq_zero
    have := hB _ lc_eval_eq_zero
    unfold r at hr; unfold lc' r at this
    rw [hr, map_zero, sub_zero] at this
    have lc_get : ∀i, lc.get i = 0 := ?_
    · ext i;rw [map_zero]
      apply lc_get
    · intro ⟨w, hw⟩; rcases hw with rfl | hw
      assumption
      rw [←LinearCombo.filter_get_mem, this, map_zero]
      assumption
  · exfalso; apply h
    have : r⁻¹? • (r • v) = r⁻¹? • (-IsModule.eval R B lc') := by
      congr; symm; apply neg_eq_of_add
      assumption
    rw [←smul_assoc, smul_eq_mul, inv?_mul_cancel, one_smul,
      ←map_neg, ←map_smul] at this
    rw [this]
    generalize r⁻¹? • -lc' = L; clear this hr lc_eval_eq_zero lc' r i lc h hB v
    induction L with
    | zero => rw [map_zero]; apply mem_zero
    | add => rw [map_add]; apply mem_add <;> assumption
    | ι i r =>
      rw [IsModule.eval_ι]
      apply mem_smul; apply Submodule.sub_span
      exact i.property
  · unfold lc' r i
    clear lc' lc_eval_eq_zero r i
    rw [map_sub, map_sub, map_sub,
      IsModule.eval_ι, LinearCombo.filter_ι_not_mem, map_zero, sub_zero]
    dsimp; induction lc with
    | zero => simp [map_zero, sub_zero, zero_smul]
    | add a b iha ihb =>
      simp [map_add, ←iha, ←ihb, add_smul]
      rw [sub_eq_add_neg, ←neg_add_neg,
        add_assoc, ←add_assoc _ (-_),
        add_comm (IsModule.eval _ _ _) (-_), ←add_assoc,
        sub_eq_add_neg, sub_eq_add_neg, ←add_assoc (_ + _), ←add_assoc]
    | ι i a =>
      obtain ⟨w, hw⟩ := i
      rw [IsModule.eval_ι]
      rcases hw with rfl | hw
      rw [LinearCombo.filter_ι_not_mem, map_zero,
        LinearCombo.get_ι_eq]; dsimp; rw [sub_self]
      dsimp; intro g; apply h
      apply Submodule.sub_span
      assumption
      rw [LinearCombo.filter_ι_mem, IsModule.eval_ι, LinearCombo.get_ι_ne, zero_smul, sub_zero]
      intro h; cases h
      apply h
      apply Submodule.sub_span
      assumption
      assumption
    dsimp; intro g; apply h
    apply Submodule.sub_span
    assumption

open Classical in
theorem filter_eval_eq
  (A B: Set V)
  (lc: LinearCombo B R)
  (s: Finset B)
  (h: ∀i, lc.get i ≠ 0 -> i.val ∈ A) :
  IsModule.eval R A ((LinearCombo.domain_sum s lc).filter R A) = IsModule.eval R B (LinearCombo.domain_sum s lc) := by
  induction s with
  | nil => simp [map_zero]
  | cons a as ha ih =>
    simp [map_add, ih]
    congr 1
    by_cases hi:lc.get a = 0
    simp [hi, map_zero]
    rw [LinearCombo.filter_ι_mem, IsModule.eval_ι, IsModule.eval_ι]
    apply h
    assumption

open Classical in
theorem eval_complete_subset
  (A B: Set V)
  (lc: LinearCombo B R)
  (h: ∀i, lc.get i ≠ 0 -> i.val ∈ A) :
  IsModule.eval R A (lc.filter R A) = IsModule.eval R B lc := by
  obtain ⟨s, hs, eq⟩ := lc.domain
  rw (occs := [1, 2]) [eq]
  rw [filter_eval_eq]
  assumption

theorem sUnion_linear_independent
  (Bs: Set (Set V))
  (hBs: ∀B ∈ Bs, IsModule.IsLinearIndependent R B)
  (Bs_chain: Bs.IsChain (· ≤ ·)):
  IsModule.IsLinearIndependent R (⋃ Bs) := by
  classical
  intro a b h
  by_cases nonempty:Bs = ⊥
  · have : ∀a: LinearCombo (⋃ Bs) R, a = 0 := ?_
    rw [this a, this b]
    clear a b h Bs_chain hBs
    subst Bs
    intro a
    induction a with
    | zero => rfl
    | add a b iha ihb => rw [iha, ihb, add_zero]
    | ι i a =>
      obtain ⟨_, hi⟩ := i
      simp at hi
  have : ∃U ∈ Bs, ∀i, a.get i ≠ 0 ∨ b.get i ≠ 0 -> i.val ∈ U := by
    have ⟨da, da_spec, ha⟩ := a.domain
    have ⟨db, db_spec, hb⟩ := b.domain
    clear ha hb
    suffices ∃U ∈ Bs, ∀i ∈ da ∪ db, i.val ∈ U by
      obtain ⟨U, U_in_Bs, spec⟩ := this
      refine ⟨U, U_in_Bs, ?_⟩
      intro i
      have := spec i; simp [←da_spec, ←db_spec] at this
      apply this
    clear da_spec db_spec
    generalize da ∪ db = domain
    clear da db h a b
    induction domain with
    | nil =>
      simp
      simp at nonempty
      obtain ⟨B, hB⟩ := nonempty
      exists B
    | cons a as a_not_in_as ih =>
      obtain ⟨B, hB, B_spec⟩ := ih
      obtain ⟨a, B', hB', a_in_B'⟩ := a
      simp
      obtain ⟨U, hU, B_sub_U, B'_sub_U⟩ : ∃U ∈ Bs, B ⊆ U ∧ B' ⊆ U := by
        have : IsTotal (Bs.Induced (· ≤ ·)) := inferInstance
        rcases total (R := Bs.Induced (· ≤ ·)) ⟨B, hB⟩ ⟨B', hB'⟩ with h | h
        exists B'
        exists B
      refine ⟨U, hU, ?_, ?_⟩
      apply B'_sub_U; assumption
      intro i V ⟨V_in_Bs, i_in_V⟩ i_in_as
      apply B_sub_U
      apply B_spec _ i_in_as
  obtain ⟨B, B_in_Bs, B_spec⟩ := this
  let a' := a.filter R B
  let b' := b.filter R B
  have : IsModule.eval R B a' = IsModule.eval R B b' := ?_
  have := hBs _ B_in_Bs this
  unfold a' b' at this
  ext i
  by_cases ha:a.get i = 0
  by_cases hb:b.get i = 0
  rw [ha, hb]
  have hi := B_spec i (.inr hb)
  rw [←LinearCombo.filter_get_mem _ _ _ a, ←LinearCombo.filter_get_mem _ _ _ b, this]
  assumption
  have hi := B_spec i (.inl ha)
  rw [←LinearCombo.filter_get_mem _ _ _ a, ←LinearCombo.filter_get_mem _ _ _ b, this]
  assumption
  unfold a' b'
  clear a' b'
  rw [eval_complete_subset, eval_complete_subset, h]
  · intro i hi; apply B_spec
    right; assumption
  · intro i hi; apply B_spec
    left; assumption

end

namespace IsModule

variable
 (R V: Type*) [FieldOps R] [IsDivisionRing R]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul R V] [IsModule R V]

public theorem basis_exists
  (R V: Type*) [FieldOps R] [IsDivisionRing R]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul R V] [IsModule R V] : ∃B: Set V, IsModule.IsBasis R B := by
  have ⟨basis, linindep, maximal⟩ := Zorn.partialorder_in (α := Set V) ({ Mem := IsModule.IsLinearIndependent R }) ?_
  · exists basis
    refine ⟨linindep, ?_⟩
    intro v; apply Classical.byContradiction
    intro not_mem_span
    have := maximal (insert v basis) ?_ (fun _ => Or.inr)
    apply not_mem_span
    rw [←this]; apply Submodule.sub_span; simp
    apply insert_linear_independent
    assumption
    assumption
  · intro U U_sub U_chain
    refine ⟨⋃ U, ?_, ?_⟩
    · apply sUnion_linear_independent
      assumption
      assumption
    · dsimp; intro u hu v hv
      exact ⟨u, hu, hv⟩

public noncomputable def basis : Set V := Classical.choose (basis_exists R V)
public theorem basis_is_basis : IsBasis R (basis R V) := Classical.choose_spec (basis_exists R V)
public theorem basis_is_linindep : IsLinearIndependent R (basis R V) := (basis_is_basis R V).linindep
public theorem basis_complete : ∀v, v ∈ Submodule.span R (basis R V) := (basis_is_basis R V).complete
