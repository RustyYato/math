import LeanMath.Data.Real.Sqrt
import LeanMath.Data.RsqrtD.Field
import LeanMath.Data.RsqrtD.Algebra
import LeanMath.Tactic.DefEqAbuse

abbrev Complex := RsqrtD ℝ (-1: ℤ)

notation "ℂ" => Complex

namespace Complex

instance (priority := 2000) : RingOps ℂ := inferInstanceAs (RingOps (RsqrtD ℝ (-1: ℤ)))
instance (priority := 2000) : IsRing ℂ := inferInstanceAs (IsRing (RsqrtD ℝ (-1: ℤ)))

def ofReal : ℝ ↪+* ℂ := RsqrtD.of_real

@[simp] def ofReal_real (r: ℝ) : (ofReal r).real = r := rfl
@[simp] def ofReal_imag (r: ℝ) : (ofReal r).imag = 0 := rfl

instance : Coe ℝ ℂ where
  coe := ofReal

instance : SMul ℚ ℂ := inferInstanceAs (SMul ℚ (RsqrtD ℝ (-1: ℤ)))
instance : AlgebraMap ℚ ℂ := inferInstanceAs (AlgebraMap ℚ (RsqrtD ℝ (-1: ℤ)))
instance : IsModule ℚ ℂ := inferInstanceAs (IsModule ℚ (RsqrtD ℝ (-1: ℤ)))
instance : IsAlgebra ℚ ℂ := inferInstanceAs (IsAlgebra ℚ (RsqrtD ℝ (-1: ℤ)))

def ofRat : ℚ ↪+* ℂ := ofReal.comp Real.ofRat

instance : HasChar ℂ 0 := HasChar.of_ring_emb ofReal

def conj : ℂ ↪+* ℂ := RsqrtD.conj

@[simp] def apply_conj_real (a: ℂ) : (conj a).real = a.real := rfl
@[simp] def apply_conj_imag (a: ℂ) : (conj a).imag = -a.imag := rfl

def conj_conj (a: ℂ) : conj (conj a) = a := RsqrtD.conj_conj _

variable [LEM]

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
instance : IsModule ℝ ℂ := inferInstanceAs (IsModule ℝ (RsqrtD ℝ (-1: ℤ)))

instance : Norm ℂ ℝ where
  norm c := (c.real ^ 2 + c.imag ^ 2).sqrt

def norm_def (c: ℂ) : ‖c‖ = (c.real ^ 2 + c.imag ^ 2).sqrt := rfl

def norm_sq (c: ℂ) : ‖c‖ ^ 2 = c.real ^ 2 + c.imag ^ 2 := by
  simp only [norm_def, Real.sq_sqrt]
  rw [abs_eq_of_nonneg]
  apply nonneg_add
  apply nonneg_sq
  apply nonneg_sq

def norm_sq_eq_mul_conj (c: ℂ) : ‖c‖^2 = c * conj c := by
  rw [←map_npow, norm_sq]
  ext; simp
  rw [←neg_smul_left, one_smul, neg_mul_right, neg_neg,
    npow_two, npow_two]
  simp
  rw [←neg_mul_right, mul_comm, neg_add_cancel]

instance : IsLawfulNorm ℂ ℝ where
  norm_nonneg a := by apply Real.nonneg_sqrt
  norm_smul a b := by
    simp [norm_def, smul_eq_mul]
    rw [mul_npow, mul_npow, ←mul_add, Real.sqrt_mul,
      Real.sqrt_sq]
  norm_add_le_add_norm a b := by
    apply Real.of_square_monotone
    · simp [norm_def]
      apply nonneg_add
      apply Real.nonneg_sqrt
      apply Real.nonneg_sqrt
    · simp [add_sq, norm_sq]
      repeat rw [add_assoc]
      apply add_le_add_left
      repeat first|rw [add_comm _ (a.imag ^ 2)]|rw [←add_assoc]
      repeat rw [add_assoc]
      apply add_le_add_left
      repeat first|rw [add_comm _ (b.real ^ 2)]|rw [←add_assoc]
      repeat rw [add_assoc]
      apply add_le_add_left
      repeat first|rw [add_comm _ (b.imag ^ 2)]|rw [←add_assoc]
      repeat rw [add_assoc]
      apply add_le_add_left
      rw [←mul_add]
      apply mul_le_mul_of_nonneg_left
      · apply Real.of_square_monotone
        apply nonneg_mul
        apply Real.nonneg_sqrt
        apply Real.nonneg_sqrt
        simp [mul_npow, norm_sq, add_sq]
        simp [mul_add, add_mul]
        repeat first|rw [add_comm _ (a.imag ^ 2 * b.imag ^ 2)]|rw [←add_assoc]
        repeat rw [add_assoc]
        apply add_le_add_left
        repeat first|rw [add_comm _ (a.real ^ 2 * b.real ^ 2)]|rw [←add_assoc]
        repeat rw [add_assoc]
        apply add_le_add_left
        have := nonneg_sq (a.imag * b.real - a.real * b.imag)
        simp [sub_sq, mul_npow, sub_add_assoc] at this
        rw [add_comm (-_), ←add_assoc, ←sub_eq_add_neg,
          le_sub_iff_add_le, zero_add] at this
        apply le_trans _ this
        apply le_of_eq
        ac_rfl
      · apply le_of_lt
        apply pos_natCast
  norm_eq_zero := by
    intro c
    apply flip Iff.intro
    intro rfl; simp [norm_def, zero_npow, add_zero]
    intro h
    have := Real.sqrt_strictMono.inj
    replace := fun x y h => @this x y h
    replace := this ⟨c.real ^ 2 + c.imag ^ 2, ?_⟩ ⟨0, le_refl _⟩
    simp at this
    replace sq_add_eq := Subtype.mk.inj (this h)
    clear this; clear this h
    apply RsqrtD.eq_zero_of_mul_conj_eq_zero
    · show c * conj c = 0
      rw [←norm_sq_eq_mul_conj, ←map_npow, norm_sq]
      ext
      simpa
      simp
    · clear this
      apply nonneg_add
      apply nonneg_sq
      apply nonneg_sq

end Complex
