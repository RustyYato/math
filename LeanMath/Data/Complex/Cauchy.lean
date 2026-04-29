import LeanMath.Data.Complex.Defs
import LeanMath.Data.Real.Sqrt

variable [LEM]

abbrev ComplexRational := RsqrtD ℚ (-1: ℤ)

abbrev ComplexRational.mk : ℚ -> ℚ -> ComplexRational := RsqrtD.mk

instance : RsqrtD.NoSolution ℚ (-1: ℤ) where
  sq_ne_r := by
    intro q h
    have := nonneg_sq  q
    rw [h] at this
    contradiction

instance : Norm ComplexRational ℚ where
  norm c := ‖c.real‖ + ‖c.imag‖

namespace ComplexRational

def norm_def (c: ComplexRational) : ‖c‖ = ‖c.real‖ + ‖c.imag‖ := rfl

instance : IsLawfulNorm ComplexRational ℚ where
  norm_nonneg a := by
    rw [norm_def]
    apply nonneg_add
    apply norm_nonneg
    apply norm_nonneg
  norm_smul a b := by
    rw [norm_def, norm_def]
    dsimp
    rw [norm_smul, norm_smul, ←mul_add]
  norm_add_le_add_norm a b := by
    dsimp [norm_def]
    apply le_trans
    apply add_le_add
    apply norm_add_le_add_norm
    apply norm_add_le_add_norm
    apply le_of_eq
    ac_rfl
  norm_eq_zero {a} := by
    symm; apply Iff.intro
    intro rfl; rfl
    show _ + _ = 0 -> _
    intro h
    by_cases ha:a.real = 0
    rw [ha, norm_zero, zero_add] at h
    ext; assumption
    apply norm_eq_zero.mp
    assumption
    have : 0 < ‖a.real‖ + ‖a.imag‖ := by
      apply flip lt_of_lt_of_le
      apply le_add_right
      apply norm_nonneg
      apply lt_of_le_of_ne
      apply norm_nonneg
      symm; intro g; apply ha
      apply norm_eq_zero.mp
      assumption
    rw [h] at this
    contradiction

instance : IsNormSubMul ComplexRational ℚ where
  norm_mul_le_mul_norm a b := by
    dsimp [norm_def]
    apply le_trans
    apply add_le_add
    apply norm_add_le_add_norm
    apply norm_add_le_add_norm
    rw [neg_zsmul, neg_norm, one_smul]
    simp [add_mul, mul_add, ←norm_mul]
    apply le_of_eq
    ac_rfl

instance : IsModule ℚ ComplexRational := inferInstance

end ComplexRational

abbrev ComplexOfCauchy := CauchySeq.Completion ComplexRational ℚ

def ComplexOfCauchy.eqv_real (a b: CauchySeq ComplexRational ℚ) (h: a ≈ b) : is_cauchy_eqv (fun i => (a i).real) (fun i => (b i).real) := by
  intro ε εpos
  have ⟨k, hk⟩ := h ε εpos
  dsimp; dsimp at hk
  exists k; intro i j hi hj
  replace hk : (_ + _) < _ := hk i j hi hj
  apply lt_of_le_of_lt _ hk
  apply le_add_right
  apply norm_nonneg

def ComplexOfCauchy.eqv_imag (a b: CauchySeq ComplexRational ℚ) (h: a ≈ b) : is_cauchy_eqv (fun i => (a i).imag) (fun i => (b i).imag) := by
  intro ε εpos
  have ⟨k, hk⟩ := h ε εpos
  dsimp; dsimp at hk
  exists k; intro i j hi hj
  replace hk : (_ + _) < _ := hk i j hi hj
  apply lt_of_le_of_lt _ hk
  apply le_add_left
  apply norm_nonneg

def ComplexOfCauchy.eqv_mk (a b c d: CauchySeq ℚ ℚ) (ac: a ≈ c) (bd: b ≈ d) : is_cauchy_eqv (fun i =>  ComplexRational.mk (a i) (b i)) (fun i => ComplexRational.mk (c i) (d i)) := by
  intro ε εpos
  have ⟨k, hk⟩ := (ac _ (pos_div?_natCast εpos 1)).merge₂ (bd _ (pos_div?_natCast εpos 1))
  dsimp; dsimp at hk
  exists k; intro i j hi hj
  replace ⟨ac, bd⟩ := hk i j hi hj
  show _ + _ < _
  dsimp
  apply lt_of_lt_of_eq
  apply add_lt_add
  exact ac
  exact bd
  rw [half_add_half]

def ComplexOfCauchy.real' (s: CauchySeq ComplexRational ℚ) : CauchySeq ℚ ℚ where
  toFun i := (s i).real
  is_cauchy' := by
    apply ComplexOfCauchy.eqv_real
    rfl

def ComplexOfCauchy.imag' (s: CauchySeq ComplexRational ℚ) : CauchySeq ℚ ℚ where
  toFun i := (s i).imag
  is_cauchy' := by
    apply ComplexOfCauchy.eqv_imag
    rfl

def ComplexOfCauchy.mk' (a b: CauchySeq ℚ ℚ) : CauchySeq ComplexRational ℚ where
  toFun i := .mk (a i) (b i)
  is_cauchy' := by
    apply ComplexOfCauchy.eqv_mk
    rfl
    rfl

def ComplexOfCauchy.real : ComplexOfCauchy -> ℝ :=
  CauchySeq.lift (fun x => Real.ofCauchySeq <| CauchySeq.ofSeq <| ComplexOfCauchy.real' x) <| by
    intro a b h
    apply Real.sound
    apply ComplexOfCauchy.eqv_real
    assumption

def ComplexOfCauchy.imag : ComplexOfCauchy -> ℝ :=
  CauchySeq.lift (fun x => Real.ofCauchySeq <| CauchySeq.ofSeq <| ComplexOfCauchy.imag' x) <| by
    intro a b h
    apply Real.sound
    apply ComplexOfCauchy.eqv_imag
    assumption

def ComplexOfCauchy.mk : ℝ -> ℝ -> ComplexOfCauchy :=
  Real.lift₂ (fun a b => CauchySeq.ofSeq (ComplexOfCauchy.mk' a b)) <| by
    intro a b c d ac bd
    apply CauchySeq.sound
    apply ComplexOfCauchy.eqv_mk
    assumption
    assumption

def Complex.equivCauchy : ℂ ≃+* ComplexOfCauchy where
  toFun c := ComplexOfCauchy.mk c.real c.imag
  invFun c := {
    real := c.real
    imag := c.imag
  }
  leftInv c := by
    induction c using CauchySeq.ind with | _ c =>
    rfl
  rightInv c := by
    obtain ⟨a, b⟩ := c
    induction a using Real.cau_ind with | _ a =>
    induction b using Real.cau_ind with | _ b =>
    rfl
  map_zero := rfl
  map_one := rfl
  map_add a b := by
    obtain ⟨a₀, a₁⟩ := a
    obtain ⟨b₀, b₁⟩ := b
    induction a₀ using Real.cau_ind with | _ =>
    induction b₀ using Real.cau_ind with | _ =>
    induction a₁ using Real.cau_ind with | _ =>
    induction b₁ using Real.cau_ind with | _ =>
    rfl
  map_mul a b := by
    obtain ⟨a₀, a₁⟩ := a
    obtain ⟨b₀, b₁⟩ := b
    induction a₀ using Real.cau_ind with | _ =>
    induction b₀ using Real.cau_ind with | _ =>
    induction a₁ using Real.cau_ind with | _ =>
    induction b₁ using Real.cau_ind with | _ =>
    rfl
