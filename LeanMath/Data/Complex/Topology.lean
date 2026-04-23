import LeanMath.Topology.MetricSpace.Prod
import LeanMath.Data.Complex.Defs

variable [LEM]

namespace Complex

instance : Metric ℂ where
  metric a b := ‖a - b‖

def metric_def (a b: ℂ) : metric a b = ‖a - b‖ := rfl

instance : IsLawfulMetric ℂ where
  metric_self a := by rw [metric_def, sub_self, norm_zero]
  metric_posdef {a b} h := by rwa [metric_def, norm_eq_zero, ←sub_eq_zero] at h
  metric_comm := norm_sub
  metric_triangle a b c := by
    iterate 3 rw [metric_def]
    rw (occs := [1]) [←add_zero (a), ←neg_add_cancel b, ←add_assoc, ←sub_eq_add_neg, add_sub_assoc]
    apply norm_add_le_add_norm

instance : TopologicalSpace ℂ := ⟨Topology.ofMetric ℂ⟩

def eqvReal₂ : ℂ ≃ₜ (ℝ × ℝ) where
  toFun c := (c.real, c.imag)
  invFun c := ⟨c.1, c.2⟩
  leftInv _ := rfl
  rightInv _ := rfl
  toFun_continuous := {
    isOpen_preimage := by
      intro S hS c hc
      simp at hc
      replace hS : S ∈ ((Topology.ofMetric ℝ).prod (Topology.ofMetric ℝ)).OpenSets := hS
      rw [Topology.prod_metric_topology] at hS
      obtain ⟨δ, δpos, h⟩ := hS _ hc
      refine ⟨δ, δpos, ?_⟩
      open IsLawfulMetric in
      intro x hx
      simp; apply h
      rw [mem_ball] at *
      apply lt_of_eq_of_lt _ hx
      simp [Prod.metric_def, Real.metric_eq_norm_sub, metric_def, norm_def]
      rw [abs_eq_max, abs_eq_max]
      congr 2
      rcases max_eq (c.real - x.real) (-(c.real - x.real)) with h | h <;> rw [h]
      rw [neg_sq]
      rcases max_eq (c.imag - x.imag) (-(c.imag - x.imag)) with h | h <;> rw [h]
      rw [neg_sq]
  }
  invFun_continuous := {
    isOpen_preimage := by
      intro S hS
      show _ ∈ ((Topology.ofMetric ℝ).prod (Topology.ofMetric ℝ)).OpenSets
      rw [Topology.prod_metric_topology]
      intro c hc
      simp at hc
      obtain ⟨δ, δpos, h⟩ := hS _ hc
      refine ⟨δ, δpos, ?_⟩
      open IsLawfulMetric in
      intro x hx
      simp; apply h
      rw [mem_ball] at *
      apply lt_of_eq_of_lt _ hx
      simp [Prod.metric_def, Real.metric_eq_norm_sub, metric_def, norm_def]
      rw [abs_eq_max, abs_eq_max]
      congr 2
      rcases max_eq (c.fst - x.fst) (-(c.fst - x.fst)) with h | h <;> rw [h]
      rw [neg_sq]
      rcases max_eq (c.snd - x.snd) (-(c.snd - x.snd)) with h | h <;> rw [h]
      rw [neg_sq]
  }

end Complex
