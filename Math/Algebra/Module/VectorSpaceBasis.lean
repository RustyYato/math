module

public import Math.Algebra.Module.Set.Basis.Group
public import Math.Algebra.Field.Defs
import Math.Order.Zorn

namespace Math

variable {R V: Type*} [FieldOps R] [IsDivisionRing R]
  [AddGroupOps V] [IsAddGroup V] [IsAddComm V]
  [SMul R V] [IsModule R V]

theorem insert_linear_independent
  (B: Set V) (v: V) (hB: IsModule.IsLinearIndependent R B) (h: v ∉ Submodule.span R B) :
  IsModule.IsLinearIndependent R (insert v B) := by
  classical
  rw [IsModule.lin_indep_iff_eq_zero_of_eval_0] at *
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
    · sorry
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

theorem sUnion_linear_independent
  (Bs: Set (Set V))
  (hBs: ∀B ∈ Bs, IsModule.IsLinearIndependent R B)
  (Bs_chain: Bs.IsChain (· ≤ ·)):
  IsModule.IsLinearIndependent R (⋃ Bs) := by
  sorry

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
