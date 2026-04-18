import LeanMath.Topology.Seperation.Defs
import LeanMath.Data.Real.Defs

variable [LEM]

class Metric (α: Type*) where
  protected metric : α -> α -> ℝ

def metric [Metric α] : α -> α -> ℝ := Metric.metric

class IsLawfulMetric (α: Type*) [Metric α] where
  protected metric_self (a: α) : metric a a = 0
  protected metric_posdef {a b: α}: metric a b = 0 -> a = b
  protected metric_comm (a b: α): metric a b = metric b a
  protected metric_triangle (a b c: α): metric a c ≤ metric a b + metric b c

def metric_self [Metric α] [IsLawfulMetric α] (a: α) : metric a a = 0 := IsLawfulMetric.metric_self _
def metric_posdef [Metric α] [IsLawfulMetric α] {a b: α}: metric a b = 0 -> a = b := IsLawfulMetric.metric_posdef
def metric_comm [Metric α] [IsLawfulMetric α] (a b: α): metric a b = metric b a := IsLawfulMetric.metric_comm _ _
def metric_triangle [Metric α] [IsLawfulMetric α] (a b c: α): metric a c ≤ metric a b + metric b c := IsLawfulMetric.metric_triangle _ _ _
def metric_nonneg [Metric α] [IsLawfulMetric α] (a b: α): 0 ≤ metric a b := by
  apply le_of_mul_le_mul_of_pos_left
  apply pos_natCast 1
  dsimp; rw [mul_zero]
  rw [two_mul]; rw (occs := [1]) [metric_comm]
  apply flip le_trans
  apply metric_triangle
  rw [metric_self]

instance : Metric ℝ where
  metric a b := ‖a - b‖
instance : Metric ℚ where
  metric a b := metric (Real.ofRat a) (Real.ofRat b)

def Real.metric_eq_norm_sub (a b: ℝ) : metric a b = ‖a - b‖ := rfl
def Rat.metric_eq_norm_sub (a b: ℚ) : metric a b = Real.ofRat ‖a - b‖ := rfl

instance : IsLawfulMetric ℝ where
  metric_self a := by rw [Real.metric_eq_norm_sub, sub_self, norm_zero]
  metric_posdef {a b} h := by rwa [Real.metric_eq_norm_sub, norm_eq_zero, ←sub_eq_zero] at h
  metric_comm := norm_sub
  metric_triangle a b c := by
    iterate 3 rw [Real.metric_eq_norm_sub]
    rw (occs := [1]) [←add_zero (a), ←neg_add_cancel b, ←add_assoc, ←sub_eq_add_neg, add_sub_assoc]
    apply norm_add_le_add_norm

instance : IsLawfulMetric ℚ where
  metric_self _ := metric_self (α := ℝ) _
  metric_posdef {a b} h := Real.ofRat.inj (metric_posdef (a := Real.ofRat a) (b := Real.ofRat b) h)
  metric_comm _ _ := metric_comm (α := ℝ) _ _
  metric_triangle _ _ _ := metric_triangle (α := ℝ) _ _ _

namespace IsLawfulMetric

variable [Metric α] [IsLawfulMetric α]

def Ball (center: α) (r: ℝ) : Set α where
  Mem x := metric center x < r

def mem_ball {center: α} {r: ℝ} : ∀{x}, x ∈ Ball center r ↔ metric center x < r := Iff.rfl
def sub_ball {center: α} {r: ℝ} : ∀{x}, x ∈ Ball center r ↔ metric center x < r := Iff.rfl
def ball_sub_ball (x: α) (δ₀ δ₁: ℝ) (h: δ₀ ≤ δ₁) : Ball x δ₀ ⊆ Ball x δ₁ := by
  intro y mem
  apply lt_of_lt_of_le (α := ℝ)
  assumption
  assumption

end IsLawfulMetric

namespace Topology

variable (α: Type*) [Metric α] [IsLawfulMetric α]

open IsLawfulMetric

-- for all points in the set, if there is an open ball which is contained in the set, then the set is open
-- this gives the same topology as Topology.generate (Ball center r)
def ofMetric : Topology α where
  IsOpen s := ∀x ∈ s, ∃δ > 0, Ball x δ ⊆ s
  open_univ := by
    intro x hx
    refine ⟨1, zero_lt_one _, fun _ _ => True.intro⟩
  open_sUnion := by
    intro U hU x ⟨u, hu, hx⟩
    have ⟨δ, δpos, hball⟩ := hU u hu x hx
    refine ⟨δ, δpos, ?_⟩
    apply Set.sub_trans hball
    apply Set.sub_sUnion
    assumption
  open_inter := by
    intro a b ha hb x ⟨hxa, hxb⟩
    have ⟨δ₀, δ₀pos, h₀⟩ := ha x hxa
    have ⟨δ₁, δ₁pos, h₁⟩ := hb x hxb
    refine ⟨δ₀ ⊓ δ₁, ?_, ?_⟩
    · apply lt_min <;> assumption
    · intro x hx
      apply And.intro
      apply h₀
      apply ball_sub_ball _ (δ₀ ⊓ δ₁) δ₀ min_le_left
      assumption
      apply h₁
      apply ball_sub_ball _ (δ₀ ⊓ δ₁) δ₁ min_le_right
      assumption

def ofMetric.BallOpen : 0 < d -> Ball a d ∈ (ofMetric α).OpenSets := by
  intro hd; intro s hs
  rw [mem_ball] at hs
  exists d - metric a s
  apply And.intro
  show 0 < _; rwa [lt_sub_iff_add_lt, zero_add]
  intro x hx
  rw [mem_ball] at *
  rw [lt_sub_iff_add_lt, add_comm] at hx
  apply lt_of_le_of_lt _ hx
  apply metric_triangle

def ofMetric.IsHausdorff : (ofMetric α).IsHausdorff := by
  intro a b h
  let d := (metric a b) /? (2: ℕ)
  have : 0 < d := by
    show 0 < _ /? _
    apply pos_div?_natCast
    rw [←not_le]
    intro g
    replace g := le_antisymm g (metric_nonneg _ _)
    have := metric_posdef g
    contradiction
  refine ⟨Ball a d, Ball b d, ?_, ?_, ?_, ?_, ?_⟩
  · apply ofMetric.BallOpen
    assumption
  · apply ofMetric.BallOpen
    assumption
  · rw [mem_ball]
    rwa [metric_self]
  · rw [mem_ball]
    rwa [metric_self]
  · simp; intro x ha hb
    rw [mem_ball] at ha hb
    rw [metric_comm] at hb
    have := add_lt_add ha hb
    rw [←two_mul, mul_comm, div?_mul_cancel] at this
    replace := lt_of_le_of_lt (metric_triangle _ _ _) this
    exact Relation.irrefl this

end Topology

instance : TopologicalSpace ℝ := ⟨Topology.ofMetric _⟩
instance : TopologicalSpace ℚ := ⟨Topology.ofMetric _⟩

instance : TopologicalSpace.IsHausdorff ℚ where
  separated_by_neighborhood_of_ne := Topology.ofMetric.IsHausdorff _
instance : TopologicalSpace.IsHausdorff ℝ where
  separated_by_neighborhood_of_ne := Topology.ofMetric.IsHausdorff _
