import LeanMath.Topology.MetricSpace.Defs
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

end Complex
