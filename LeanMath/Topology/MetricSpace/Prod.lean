import LeanMath.Topology.MetricSpace.Defs
import LeanMath.Data.Real.Sqrt

variable [LEM]

instance [Metric α] [Metric β] : Metric (α × β) where
  metric x y := (metric x.1 y.1 ^ 2 + metric x.2 y.2 ^ 2).sqrt

def Prod.metric_def [Metric α] [Metric β] (x y: α × β) :
  metric x y = (metric x.1 y.1 ^ 2 + metric x.2 y.2 ^ 2).sqrt := rfl

def Prod.sq_metric [Metric α] [Metric β] (x y: α × β) :
  metric x y ^ 2 = metric x.1 y.1 ^ 2 + metric x.2 y.2 ^ 2 := by
  rw [metric_def, Real.sq_sqrt, abs_eq_of_nonneg]
  apply nonneg_add
  apply nonneg_sq
  apply nonneg_sq

instance [Metric α] [Metric β] [IsLawfulMetric α] [IsLawfulMetric β] : IsLawfulMetric (α × β) where
  metric_self a := by
    rw [Prod.metric_def, metric_self, metric_self,
      zero_npow, add_zero, Real.sqrt_zero]
    decide
  metric_comm a b := by
    rw [Prod.metric_def, Prod.metric_def,
      metric_comm, metric_comm a.snd]
  metric_posdef {a b} h := by
    replace h := Real.of_sqrt_eq_zero _ h
    ext
    rw [←neg_neg (metric a.snd b.snd ^ 2), ←sub_eq_add_neg, ←sub_eq_zero] at h
    apply metric_posdef
    symm; apply le_antisymm
    apply metric_nonneg
    apply Real.of_square_monotone
    rfl; rw [zero_npow_succ, ←neg_zero, h, neg_le_neg_iff]
    apply nonneg_sq

    rw [add_comm, ←neg_neg (metric a.fst b.fst ^ 2), ←sub_eq_add_neg, ←sub_eq_zero] at h
    apply metric_posdef
    symm; apply le_antisymm
    apply metric_nonneg
    apply Real.of_square_monotone
    rfl; rw [zero_npow_succ, ←neg_zero, h, neg_le_neg_iff]
    apply nonneg_sq
  metric_triangle := by
    intro x y z
    apply Real.of_square_monotone
    apply nonneg_add
    apply Real.nonneg_sqrt
    apply Real.nonneg_sqrt
    simp [add_sq, Prod.sq_metric]
    simp [Prod.metric_def]
    rw [←Real.sqrt_mul]
    simp [add_mul, mul_add]
    let a := metric x.fst y.fst
    let b := metric y.fst z.fst
    let c := metric x.fst z.fst
    let p := metric x.snd y.snd
    let q := metric y.snd z.snd
    let r := metric x.snd z.snd
    let d := a ^ 2 * b ^ 2 + p ^ 2 * b ^ 2 + (a ^ 2 * q ^ 2 + p ^ 2 * q ^ 2)
    have c_le : c ≤ a + b := metric_triangle _ _ _
    have r_le : r ≤ p + q := metric_triangle _ _ _
    show c ^ 2 + r ^ 2 ≤ (((a ^ 2 + p ^ 2) + (2: ℕ) * Real.sqrt d) + (b ^ 2 + q ^ 2))
    rw [add_comm_right, add_comm _ ((2: ℕ) * d.sqrt), le_add_iff_sub_le]
    apply le_trans
    show _ ≤ (2: ℕ) * (a * b + p * q)
    rw [sub_le_iff_le_add,
      mul_add, show
        (2: ℕ) * (a * b) + (2: ℕ) * (p * q) + (a ^ 2 + p ^ 2 + (b ^ 2 + q ^ 2)) =
        (a ^ 2 + (2: ℕ) * (a * b) + b ^ 2) + (p ^ 2 + (2: ℕ) * (p * q) + q ^ 2) by ac_rfl
    ]
    rw [←add_sq, ←add_sq]
    apply add_le_add
    apply Real.square_monotone
    apply metric_nonneg
    assumption
    apply Real.square_monotone
    apply metric_nonneg
    assumption
    apply mul_le_mul_of_nonneg_left _ _ (nonneg_natCast _)
    apply Real.of_square_monotone
    apply Real.nonneg_sqrt
    rw [Real.sq_sqrt, abs_eq_of_nonneg _ (by
      apply nonneg_add
      iterate 2
        apply nonneg_add
        iterate 2
          apply nonneg_mul
          apply nonneg_sq
          apply nonneg_sq)]
    rw [add_sq]; unfold d; clear d
    simp [←mul_npow]
    rw [add_comm_right, add_assoc _ _ (_ + _),
      ←add_assoc _ _ ((p * q) ^ 2),
      add_comm_right _ _ ((p * q) ^ 2),
      add_comm ((p * b) ^ 2) ((p * q) ^ 2),
      ←add_assoc (_ ^ 2),
      ←add_assoc (_ ^ 2),
      add_assoc (_ + _)]
    apply add_le_add_left
    have := nonneg_sq (p * b - a * q)
    simp [sub_sq, mul_npow, sub_add_assoc] at this
    rw [add_comm (-_), ←add_assoc, ←sub_eq_add_neg,
      le_sub_iff_add_le, zero_add] at this
    rw [mul_npow, mul_npow]
    apply le_trans _ this
    apply le_of_eq
    ac_rfl

namespace Topology

def prod_metric_topology [Metric α] [Metric β] [IsLawfulMetric α] [IsLawfulMetric β] : (ofMetric α).prod (ofMetric β) = ofMetric (α × β) := by
  ext s
  apply Iff.intro
  · intro h
    apply of_mem_generate h
    intro x hx
    rcases hx with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · intro (a, b) h; simp at h
      obtain ⟨δ, δpos, hδ⟩  := hx a h
      refine ⟨δ, δpos, ?_⟩
      intro (c, d); intro g
      apply hδ
      dsimp
      rw [IsLawfulMetric.mem_ball] at *
      apply lt_of_le_of_lt _ g
      simp [Prod.metric_def]
      rw [←abs_eq_of_nonneg (metric a c) (metric_nonneg _ _),
        ←Real.sqrt_sq]
      apply (Real.sqrt_strictMono.le_iff_le (a := ⟨_, by
        apply nonneg_sq⟩) (b := ⟨_, by
        apply nonneg_add
        apply nonneg_sq
        apply nonneg_sq⟩)).mpr
      rw [show ∀{P: ℝ -> Prop} (a b: Subtype P), a ≤ b ↔ a.val ≤ b.val from fun _ _ => Iff.rfl]
      simp
      rw [abs_eq_of_nonneg]
      apply le_add_right
      apply nonneg_sq
      apply metric_nonneg
    · intro (a, b) h; simp at h
      obtain ⟨δ, δpos, hδ⟩  := hx b h
      refine ⟨δ, δpos, ?_⟩
      intro (c, d); intro g
      apply hδ
      dsimp
      rw [IsLawfulMetric.mem_ball] at *
      apply lt_of_le_of_lt _ g
      simp [Prod.metric_def]
      rw [←abs_eq_of_nonneg (metric b d) (metric_nonneg _ _),
        ←Real.sqrt_sq]
      apply (Real.sqrt_strictMono.le_iff_le (a := ⟨_, by
        apply nonneg_sq⟩) (b := ⟨_, by
        apply nonneg_add
        apply nonneg_sq
        apply nonneg_sq⟩)).mpr
      rw [show ∀{P: ℝ -> Prop} (a b: Subtype P), a ≤ b ↔ a.val ≤ b.val from fun _ _ => Iff.rfl]
      simp
      rw [abs_eq_of_nonneg]
      apply le_add_left
      apply nonneg_sq
      apply metric_nonneg
  · intro h
    open IsLawfulMetric in
    -- let B : Set (Set (α × β)) := {
    --   Mem u := u ⊆ s ∧ ∃x r, 0 < r ∧ Ball x r = u
    -- }
    -- have : s = ⋃ B := by
    --   ext x; apply Iff.intro
    --   intro hx
    --   have ⟨r, hr, sub⟩ := h x hx
    --   simp; exists Ball x r
    --   apply And.intro
    --   exact ⟨sub, x, r, hr, rfl⟩
    --   rwa [mem_ball, metric_self]
    --   simp; rintro _ ⟨sub, x, r, hr, rfl⟩
    --   apply sub
    -- rw [this]
    -- clear h this
    -- apply OpenSets.sUnion
    -- rintro _ ⟨sub, x, r, hr, rfl⟩
    -- apply Generate.of
    -- left; show ∃t, _

    let B : Set (Set (α × β)) := {
      Mem x :=
        x ⊆ s ∧
        ∃(u: Set α) (v: Set β),
        x = Set.preimage Prod.fst u ∩ Set.preimage Prod.snd v ∧
        u ∈ (ofMetric α).OpenSets ∧
        v ∈ (ofMetric β).OpenSets
    }
    rw [show s = ⋃B from ?_]
    · apply OpenSets.sUnion
      rintro _ ⟨_, u, v, rfl, hu, hv⟩
      apply OpenSets.inter
      apply OpenSets.preimage _ (ofMetric α)
      assumption
      apply OpenSets.preimage _ (ofMetric β)
      assumption
    · ext ⟨a, b⟩
      symm; apply Iff.intro
      intro hx; simp at hx
      obtain ⟨_, ⟨sub, u, v, rfl, hu, hv⟩, hu', hv'⟩ := hx
      · apply sub
        apply And.intro
        assumption
        assumption
      · intro hx
        have ⟨δ, δpos, ball_sub⟩ := h _ hx
        let ε := δ /? Real.sqrt (2: ℕ)
        have εpos : 0 < ε := by
          apply pos_div?
          assumption
          apply lt_of_le_of_ne; apply Real.nonneg_sqrt
          symm; invert_tactic
        let s' := (IsLawfulMetric.Ball a ε).preimage Prod.fst
          ∩ (IsLawfulMetric.Ball b ε).preimage Prod.snd
        refine ⟨s', ?_, by simp [s', mem_ball, metric_self, εpos]⟩
        refine ⟨?_, _, _, rfl, ?_, ?_⟩
        intro x hx
        · intros
          simp [s'] at hx
          apply ball_sub
          obtain ⟨ha, hb⟩ := hx
          rw [mem_ball] at *
          rw [Prod.metric_def]; dsimp
          apply lt_of_lt_of_le
          apply Real.sqrt_strictMono (a := ⟨_, _⟩) (b := ⟨_, _⟩)
          apply add_lt_add (α := ℝ)
          apply Real.square_strict_monotone
          apply metric_nonneg
          assumption
          apply Real.square_strict_monotone
          apply metric_nonneg
          assumption
          apply nonneg_add
          apply nonneg_sq
          apply nonneg_sq
          apply nonneg_add
          apply nonneg_sq
          apply nonneg_sq
          dsimp [ε]
          rw [npow_div?]
          simp [abs_eq_of_nonneg _ (nonneg_natCast _)]
          rw [half_add_half]
          rw [Real.sqrt_sq, abs_eq_of_nonneg]
          apply le_of_lt
          assumption
        · apply ofMetric.BallOpen
          assumption
        · apply ofMetric.BallOpen
          assumption

end Topology
