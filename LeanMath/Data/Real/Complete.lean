import LeanMath.Data.Real.Lattice

namespace Real

variable [LEM]

private def set (c: CauchySeq.Completion ℝ ℝ) : Set ℝ where
  Mem r := CauchySeq.Completion.const r ≤ c

@[implicit_reducible]
private def set_nonempty (c: CauchySeq.Completion ℝ ℝ) : (set c).Nonempty := by
  cases c using CauchySeq.ind with | _ c =>
  have ⟨B, hB⟩ := (-c).bounded
  exists -B; dsimp [set]
  apply CauchySeq.le_of_eventually_le
  exists 0; intro i hi; dsimp
  rw [←neg_le_neg_iff, neg_neg]
  have := hB i
  rw [abs_eq_max] at this
  apply le_trans left_le_max (le_of_lt this)

private def set_bounded (c: CauchySeq.Completion ℝ ℝ) : (set c).BoundedAbove := by
  cases c using CauchySeq.ind with | _ c =>
  have ⟨B, Bpos, hB⟩ := c.bounded_with 0
  exists B /? (2: ℕ) + B
  intro r hr
  replace ⟨c', eqv_c', even⟩ : CauchySeq.IsNonneg (c - CauchySeq.const r) := hr
  have ⟨i, hi⟩ := (eqv_c' (B /? (2: ℕ)) ?_).merge even
  replace hci := (hi i i (le_refl _) (le_refl _)).right
  replace hi : ‖c i - r - c' i‖ < _ := (hi i i (le_refl _) (le_refl _)).left
  rw [norm_sub, abs_eq_max] at hi
  replace hi := lt_of_le_of_lt left_le_max hi
  rw [sub_lt_iff_lt_add] at hi
  replace hi := lt_of_le_of_lt hci hi
  rw [←add_sub_assoc, lt_sub_iff_add_lt, zero_add] at hi
  apply le_trans; apply le_of_lt; assumption
  apply add_le_add_left
  apply le_trans _ (le_of_lt (hB i))
  rw [abs_eq_max]; apply left_le_max
  apply pos_div?_natCast
  assumption

def CauchySeq.forall_gt_neg_of_nonneg (c: CauchySeq ℝ ℝ) : c.IsNonneg -> ∀ε, 0 < ε -> CauchySeq.Eventually fun i => -ε < c i := by
  intro c_nonneg ε εpos
  obtain ⟨c', eqv, hc'⟩ := c_nonneg
  have := eqv _ (pos_div?_natCast εpos 1) |>.merge hc'; dsimp at this
  obtain ⟨k, hk⟩ := this; exists k
  intro i hi
  replace ⟨eqv, hk⟩ := hk i i hi hi
  rw [norm_sub, abs_eq_max] at eqv
  replace eqv := lt_of_le_of_lt left_le_max eqv
  rw [sub_lt_iff_lt_add] at eqv
  replace eqv := lt_of_le_of_lt hk eqv
  rw [add_comm, ←sub_lt_iff_lt_add, zero_sub] at eqv
  rw [←half_add_half ε]
  apply lt_trans _ eqv
  rw [neg_lt_neg_iff]
  rw (occs := [1]) [←add_zero (_ /? _)]
  apply add_lt_add_left
  apply pos_div?_natCast
  assumption

def CauchySeq.exists_lt_neg_of_neg (c: CauchySeq ℝ ℝ) : ¬c.IsNonneg -> ∃ε, 0 < ε ∧ CauchySeq.Eventually fun i => c i < -ε := by
  intro c_nonneg
  rcases Relation.trichotomous (fun a b => (b - a).IsPos) 0 c.ofSeq with h | h | h
  rw [sub_zero] at h
  have := CauchySeq.nonneg_of_pos _ h; contradiction
  have : CauchySeq.Completion.IsNonneg (γ := ℝ) 0 := CauchySeq.nonneg_of_zero (γ := ℝ)
  rw [h] at this; contradiction
  rw [zero_sub] at h
  obtain ⟨B, hB, k, hk⟩ := h
  refine ⟨B, hB, k, ?_⟩
  intro i hi
  have := hk i hi
  rwa [←neg_lt_neg_iff, neg_neg]

def complete (c: CauchySeq.Completion ℝ ℝ) : ∃r: ℝ, c = .const r := by
  let L := ⨆ (set c)
  exists L
  cases c using CauchySeq.ind with | _ c =>
  apply CauchySeq.sound; intro ε εpos; dsimp
  have ⟨r, r_mem, hr⟩ := lt_mem_of_lt_csSup (set c.ofSeq) (set_nonempty _)
    (a := L - ε /? (2: ℕ)) (by
    show _ < L
    rw [sub_eq_add_neg]; rw (occs := [2]) [←add_zero L]
    apply add_lt_add_left
    rw [←neg_lt_neg_iff, neg_neg, neg_zero]
    apply pos_div?_natCast
    assumption)
  have L_sub_lt := CauchySeq.forall_gt_neg_of_nonneg _ r_mem (ε /? (2: ℕ)) (pos_div?_natCast εpos 1)
  replace L_sub_lt : CauchySeq.Eventually fun i => L - ε < c i := by
    obtain ⟨k, hk⟩ := L_sub_lt
    exists k; intro i hi
    have : _ < c i - r := hk i hi; dsimp at this
    rw [←half_add_half ε, sub_add, sub_eq_add_neg]; apply lt_trans
    apply add_lt_add_right
    assumption
    rwa [add_comm, add_lt_iff_lt_sub]
  have L_add_gt : c.ofSeq < CauchySeq.Completion.const (L + ε) := by
    rw [←not_le]; intro h
    have : L + ε ≤ L := le_csSup (set_bounded c.ofSeq) h
    rw [←not_lt] at this; apply this; clear this
    rw (occs := [1]) [←add_zero L]
    apply add_lt_add_left
    assumption
  replace ⟨δ, δpos, L_add_gt⟩ := CauchySeq.exists_lt_neg_of_neg _ (not_le.mpr L_add_gt)
  replace L_add_gt : CauchySeq.Eventually fun i => c i - (L + ε) < -δ  := L_add_gt
  obtain ⟨k, hk⟩ := L_sub_lt.merge L_add_gt
  exists k; intro i j hi hj; clear j hj
  have ⟨L_sub_lt, L_add_gt⟩ := hk i hi
  replace L_add_gt : c i - (L + ε) < 0 := by
    apply lt_trans L_add_gt
    rwa [←neg_lt_neg_iff, neg_neg, neg_zero]
  rw [sub_lt_iff_lt_add, add_comm, ←sub_lt_iff_lt_add] at L_sub_lt
  rw [←neg_lt_neg_iff, neg_zero, neg_sub, add_comm, add_sub_assoc,
    add_comm, ←sub_lt_iff_lt_add,
    sub_eq_add_neg, zero_add] at L_add_gt
  rw [norm_sub, abs_eq_max]
  rcases le_total (L - c i) (-(L - c i)) with h | h
  rwa [max_eq_right h, ←neg_lt_neg_iff, neg_neg]
  rwa [max_eq_left h]

def CauchySeq.constHom : ℝ →+* CauchySeq.Completion ℝ ℝ where
  toFun := CauchySeq.Completion.const
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

private def complete' (c: CauchySeq.Completion ℝ ℝ) : existsUnique fun r: ℝ => c = .const r := by
  obtain ⟨r, hr⟩ := complete c
  refine ⟨r, hr, ?_⟩
  intro s hs; rw [hs] at hr; clear hs
  exact (inj CauchySeq.constHom hr).symm

noncomputable section

private def lim' (c: CauchySeq.Completion ℝ ℝ) : ℝ := Classical.choose_unique (complete' c)

private def lim'_const (r: ℝ) : lim' (CauchySeq.Completion.const r) = r := by
  have := Classical.choose_unique_spec (complete' (CauchySeq.Completion.const r))
  exact (inj CauchySeq.constHom this).symm

@[irreducible]
def lim : CauchySeq.Completion ℝ ℝ →+* ℝ where
  toFun := lim'
  map_zero := lim'_const _
  map_one := lim'_const _
  map_add a b := by
    obtain ⟨a, rfl⟩ := complete a
    obtain ⟨b, rfl⟩ := complete b
    show lim' (CauchySeq.Completion.const (a + b)) = _
    iterate 3 rw [lim'_const]
  map_mul a b := by
    obtain ⟨a, rfl⟩ := complete a
    obtain ⟨b, rfl⟩ := complete b
    show lim' (CauchySeq.Completion.const (a * b)) = _
    iterate 3 rw [lim'_const]

private def lim_const (r: ℝ) : lim (CauchySeq.Completion.const r) = r := by
  unfold lim
  apply lim'_const

end

end Real
