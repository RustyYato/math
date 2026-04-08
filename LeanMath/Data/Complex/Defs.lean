import LeanMath.Data.Real.Defs
import LeanMath.Data.RsqrtD.Field
import LeanMath.Data.RsqrtD.Algebra

variable [LEM]

abbrev Complex := RsqrtD ℝ (-1: ℤ)

notation "ℂ" => Complex

namespace Complex

instance : RsqrtD.NoSolution ℝ (-1: ℤ) where
  sq_ne_r a h := by
    replace h : a ^ 2 = -1 := h
    have : 0 ≤ a ^ 2 := by
      rw [npow_succ, npow_one]
      rcases le_total 0 a with h | h
      · rw [←mul_zero a]
        apply mul_le_mul_of_nonneg_left
        assumption; assumption
      · rw [←neg_neg (a * a), neg_mul_right, neg_mul_left]
        rw [←mul_zero (-a)]
        apply mul_le_mul_of_nonneg_left
        iterate 2
        rw [←neg_zero]; apply neg_le_neg
        assumption
    rw [h, ←not_lt] at this
    apply this; clear this h
    apply (intCast_lt_intCast _ _).mpr
    decide

instance : FieldOps ℂ := inferInstanceAs (FieldOps (RsqrtD ℝ (-1: ℤ)))
instance : IsField ℂ := inferInstanceAs (IsField (RsqrtD ℝ (-1: ℤ)))
instance : SMul ℝ ℂ := inferInstanceAs (SMul ℝ (RsqrtD ℝ (-1: ℤ)))
instance : AlgebraMap ℝ ℂ := inferInstanceAs (AlgebraMap ℝ (RsqrtD ℝ (-1: ℤ)))
instance : IsAlgebra ℝ ℂ := inferInstanceAs (IsAlgebra ℝ (RsqrtD ℝ (-1: ℤ)))

def ofReal : ℝ ↪+* ℂ := RsqrtD.of_real
instance : HasChar ℂ 0 := HasChar.of_ring_emb ofReal

def conj : ℂ ↪+* ℂ := RsqrtD.conj

def apply_conj_real (a: ℂ) : (conj a).real = a.real := rfl
def apply_conj_imag (a: ℂ) : (conj a).imag = -a.imag := rfl

def conj_conj (a: ℂ) : conj (conj a) = a := RsqrtD.conj_conj _

end Complex
