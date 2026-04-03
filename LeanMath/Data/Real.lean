import LeanMath.Data.CauSeq.Defs
import LeanMath.Data.Rational.Norm
import LeanMath.Algebra.Algebra.Ring

variable [LEM]

def Real := CauchySeq.Completion ℚ ℚ

notation "ℝ" => Real

namespace Real

section

-- unseal Real

instance : FieldOps ℝ := inferInstanceAs (FieldOps (CauchySeq.Completion ℚ ℚ))
instance : IsField ℝ := inferInstanceAs (IsField (CauchySeq.Completion ℚ ℚ))
instance : LT ℝ := inferInstanceAs (LT (CauchySeq.Completion ℚ ℚ))
instance : LE ℝ := inferInstanceAs (LE (CauchySeq.Completion ℚ ℚ))
instance : IsZeroLEOne ℝ := inferInstanceAs (IsZeroLEOne (CauchySeq.Completion ℚ ℚ))
instance : IsLinearOrder ℝ := inferInstanceAs (IsLinearOrder (CauchySeq.Completion ℚ ℚ))
instance : IsStrictOrderedSemiring ℝ := inferInstanceAs (IsStrictOrderedSemiring (CauchySeq.Completion ℚ ℚ))

instance : SMul ℚ ℝ := inferInstanceAs (SMul ℚ (CauchySeq.Completion ℚ ℚ))
instance : AlgebraMap ℚ ℝ := inferInstanceAs (AlgebraMap ℚ (CauchySeq.Completion ℚ ℚ))
instance : IsAlgebra ℚ ℝ := CauchySeq.instIsAlgebraCompletion
instance : IsModule ℚ ℝ := inferInstance

def ofRat : ℚ ↪+* ℝ where
    toRingHom := algebraMap ℚ
    inj := inj (algebraMap ℚ (α := ℝ))

instance : AlgebraMap ℤ ℝ := inferInstance
instance : IsAlgebra ℤ ℝ := inferInstance
instance : AlgebraMap ℕ ℝ := inferInstance
instance : IsAlgebra ℕ ℝ := inferInstance

instance : Norm ℝ ℝ := inferInstanceAs (Norm (CauchySeq.Completion ℚ ℚ) (CauchySeq.Completion ℚ ℚ))
instance : IsLawfulAbs ℝ := inferInstanceAs (IsLawfulAbs (CauchySeq.Completion ℚ ℚ))
instance : IsAbsMax ℝ := inferInstanceAs (IsAbsMax (CauchySeq.Completion ℚ ℚ))

instance : Min ℝ where
    min a b := (a + b - ‖a - b‖) /? (2: ℕ)
instance : Max ℝ where
    max a b := (a + b + ‖a - b‖) /? (2: ℕ)

private def min_def (a b: ℝ) : a ⊓ b = (a + b - ‖a - b‖) /? (2: ℕ) := rfl
private def max_def (a b: ℝ) : a ⊔ b = (a + b + ‖a - b‖) /? (2: ℕ) := rfl

private protected def max_comm (a b: ℝ) : a ⊔ b = b ⊔ a := by
  rw [max_def, max_def, add_comm a, norm_sub]
private protected def min_comm (a b: ℝ) : a ⊓ b = b ⊓ a := by
  rw [min_def, min_def, add_comm a, norm_sub]
private protected def min_le_left (a b: ℝ) : a ⊓ b ≤ a := by
    rw [min_def]
    have := mul_le_mul_of_nonneg_right (b := a * (2: ℕ)) (a := a + b - ‖a - b‖) (c := (2: ℕ)⁻¹?)
    rw [mul_assoc, mul_inv?_cancel, mul_one, ←div?_eq_mul_inv?] at this
    apply this
    · rw [←nsmul_eq_mul_natCast, succ_nsmul, one_nsmul, add_sub_assoc]
      apply add_le_add_left
      apply le_of_add_le_add_right
      rw [sub_add_assoc, neg_add_cancel, add_zero]
      apply le_of_add_le_add_left
      rw [←add_assoc, neg_add_cancel a, zero_add, add_comm, norm_sub, ←sub_eq_add_neg]
      induction a using CauchySeq.ind with | _ a =>
      induction b using CauchySeq.ind with | _ b =>
      apply CauchySeq.le_of_eventually_le
      exists 0; intro i hi
      show b i - a i ≤ ‖b i - a i‖
      rw [abs_eq_max]
      apply left_le_max
    · apply le_of_lt
      apply pos_inv?
      apply pos_natCast

private protected def left_le_max (a b: ℝ) : a ≤ a ⊔ b := by
    rw [max_def]
    have := mul_le_mul_of_nonneg_right (a := a * (2: ℕ)) (b := a + b + ‖a - b‖) (c := (2: ℕ)⁻¹?)
    rw [mul_assoc, mul_inv?_cancel, mul_one, ←div?_eq_mul_inv?] at this
    apply this
    · rw [←nsmul_eq_mul_natCast, succ_nsmul, one_nsmul, add_assoc]
      apply add_le_add_left
      rw [add_comm]
      apply le_of_add_le_add_right
      rw [add_assoc, add_neg_cancel b, add_zero, ←sub_eq_add_neg]
      induction a using CauchySeq.ind with | _ a =>
      induction b using CauchySeq.ind with | _ b =>
      apply CauchySeq.le_of_eventually_le
      exists 0; intro i hi
      show a i - b i ≤ ‖a i - b i‖
      rw [abs_eq_max]
      apply left_le_max
    · apply le_of_lt
      apply pos_inv?
      apply pos_natCast

private protected def max_eq_of_le {a b: ℝ} (h: a ≤ b) : a ⊔ b = b := by
  rw [max_def, norm_sub, abs_eq_of_nonneg, add_comm, sub_add_assoc, ←add_assoc (-a), neg_add_cancel, zero_add]
  rw (occs := [1]) [←one_nsmul b, ←succ_nsmul, nsmul_eq_mul_natCast, mul_div?_assoc, div?_self, mul_one]
  apply le_of_add_le_add_right
  rwa [sub_add_assoc, neg_add_cancel, add_zero, zero_add]
private protected def max_eq (a b: ℝ) : a ⊔ b = a ∨ a ⊔ b = b := by
  rcases le_total a b with h | h
  right; rw [max_eq_of_le h]
  left; rw [max_comm, max_eq_of_le h]

private protected def min_eq_of_le {a b: ℝ} (h: a ≤ b) : a ⊓ b = a := by
  rw [min_def, norm_sub, abs_eq_of_nonneg, sub_eq_add_neg, neg_sub, sub_eq_add_neg, add_assoc, add_left_comm b, add_neg_cancel, add_zero]
  rw (occs := [1]) [←one_nsmul a, ←succ_nsmul, nsmul_eq_mul_natCast, mul_div?_assoc, div?_self, mul_one]
  apply le_of_add_le_add_right
  rwa [sub_add_assoc, neg_add_cancel, add_zero, zero_add]
private protected def min_eq (a b: ℝ) : a ⊓ b = a ∨ a ⊓ b = b := by
  rcases le_total a b with h | h
  left; rw [min_eq_of_le h]
  right; rw [min_comm, min_eq_of_le h]

instance : IsLattice ℝ where
    left_le_max := left_le_max _ _
    right_le_max := by intro a b; rw [max_comm]; apply left_le_max
    max_le := by
      intro x a b ha hb
      rcases max_eq a b with h | h <;> rwa [h]
    min_le_left := min_le_left _ _
    min_le_right := by intro a b; rw [min_comm]; apply min_le_left
    le_min := by
      intro x a b ha hb
      rcases min_eq a b with h | h <;> rwa [h]

end

instance : HasChar ℝ 0 := HasChar.of_ring_emb ofRat

end Real
