import LeanMath.Data.Complex.Defs
import LeanMath.Data.Real.Complete
import LeanMath.Data.Real.Sqrt

variable [LEM]

def ComplexCauchy.eqv_real (a b: CauchySeq ℂ ℝ) (h: a ≈ b) : is_cauchy_eqv (fun i => (a i).real) (fun i => (b i).real) := by
  intro ε εpos
  have ⟨k, hk⟩ := h ε εpos
  dsimp; dsimp at hk
  exists k; intro i j hi hj
  replace hk := hk i j hi hj
  apply lt_of_le_of_lt _ hk
  rw [←Real.sqrt_sq]
  apply Real.sqrt_mono (a := ⟨_, _⟩) (b := ⟨_, _⟩)
  apply le_add_right (α := ℝ)
  apply nonneg_sq
  apply nonneg_sq
  apply nonneg_add
  apply nonneg_sq
  apply nonneg_sq

def ComplexCauchy.eqv_imag (a b: CauchySeq ℂ ℝ) (h: a ≈ b) : is_cauchy_eqv (fun i => (a i).imag) (fun i => (b i).imag) := by
  intro ε εpos
  have ⟨k, hk⟩ := h ε εpos
  dsimp; dsimp at hk
  exists k; intro i j hi hj
  replace hk := hk i j hi hj
  apply lt_of_le_of_lt _ hk
  rw [←Real.sqrt_sq]
  apply Real.sqrt_mono (a := ⟨_, _⟩) (b := ⟨_, _⟩)
  apply le_add_left (α := ℝ)
  apply nonneg_sq
  apply nonneg_sq
  apply nonneg_add
  apply nonneg_sq
  apply nonneg_sq

abbrev Complex.mk : ℝ -> ℝ -> ℂ := RsqrtD.mk

def abs_sq (a: ℝ) : ‖a‖ ^ 2 = a ^ 2 := by
  rw [abs_eq_max]
  rcases max_eq a (-a) with h | h <;> rw [h]
  rw [neg_sq]

def ComplexCauchy.eqv_mk (a b c d: CauchySeq ℝ ℝ) (ac: a ≈ c) (bd: b ≈ d) : is_cauchy_eqv (fun i => Complex.mk (a i) (b i)) (fun i => Complex.mk (c i) (d i)) := by
  intro ε εpos
  let δ := ε /? Real.sqrt (2: ℕ)
  have δpos : 0 < δ := by
    apply pos_div?
    assumption
    apply lt_of_le_of_ne
    apply Real.nonneg_sqrt
    symm; invert_tactic
  have ⟨k, hk⟩ := (ac δ δpos).merge₂ (bd δ δpos)
  dsimp; dsimp at hk
  exists k; intro i j hi hj
  replace ⟨ac, bd⟩ := hk i j hi hj
  show Real.sqrt (_ + _) < _
  dsimp
  apply Real.of_square_strict_monotone
  apply le_of_lt; assumption
  rw [Real.sq_sqrt, abs_eq_of_nonneg]
  apply lt_of_lt_of_eq
  apply add_lt_add
  rw [←abs_sq]
  apply Real.square_strict_monotone
  apply norm_nonneg
  assumption
  rw [←abs_sq]
  apply Real.square_strict_monotone
  apply norm_nonneg
  assumption
  unfold δ
  simp [npow_div?, abs_eq_of_nonneg _ (nonneg_natCast _)]
  rw [half_add_half]
  apply nonneg_add
  apply nonneg_sq
  apply nonneg_sq

def ComplexCauchy.real' (c: CauchySeq ℂ ℝ) : CauchySeq ℝ ℝ where
  toFun i := (c i).real
  is_cauchy' := by
    apply ComplexCauchy.eqv_real
    rfl

def ComplexCauchy.imag' (c: CauchySeq ℂ ℝ) : CauchySeq ℝ ℝ where
  toFun i := (c i).imag
  is_cauchy' := by
    apply ComplexCauchy.eqv_imag
    rfl

def ComplexCauchy.real : CauchySeq.Completion ℂ ℝ -> CauchySeq.Completion ℝ ℝ :=
  CauchySeq.lift (fun c => CauchySeq.ofSeq <| {
    toFun i := (c i).real
    is_cauchy' := by
      apply ComplexCauchy.eqv_real
      rfl
  }) <| by
    intro a b h
    apply CauchySeq.sound
    apply ComplexCauchy.eqv_real
    assumption

def ComplexCauchy.imag : CauchySeq.Completion ℂ ℝ -> CauchySeq.Completion ℝ ℝ :=
  CauchySeq.lift (fun c => CauchySeq.ofSeq <| {
    toFun i := (c i).imag
    is_cauchy' := by
      apply ComplexCauchy.eqv_imag
      rfl
  }) <| by
    intro a b h
    apply CauchySeq.sound
    apply ComplexCauchy.eqv_imag
    assumption

def ComplexCauchy.mk : CauchySeq.Completion ℝ ℝ -> CauchySeq.Completion ℝ ℝ -> CauchySeq.Completion ℂ ℝ :=
  CauchySeq.lift₂ (fun a b => CauchySeq.ofSeq <| {
    toFun i := {
      real := a i
      imag := b i
    }
    is_cauchy' := by
      apply ComplexCauchy.eqv_mk
      rfl
      rfl
  }) <| by
    intro a b c d ac bd
    apply CauchySeq.sound
    apply ComplexCauchy.eqv_mk
    assumption
    assumption

def ComplexCauchy.eta (c: CauchySeq.Completion ℂ ℝ) : mk (real c) (imag c) = c := by
  induction c; rfl

@[ext]
def ComplexCauchy.ext (a b: CauchySeq.Completion ℂ ℝ) :
  real a = real b -> imag a = imag b -> a = b
   := by
  intro r i
  rw [←eta a, ←eta b, r, i]

namespace Complex

def complete : ∀s: CauchySeq.Completion ℂ ℝ, ∃c: ℂ, s = CauchySeq.Completion.const c := by
  intro s
  let r := ComplexCauchy.real s
  let i := ComplexCauchy.imag s
  exists {
    real := Real.lim r
    imag := Real.lim i
  }
  ext
  all_goals
  symm; apply Real.const_lim

private def complete' (c: CauchySeq.Completion ℂ ℝ) : existsUnique fun r: ℂ => c = .const r := by
  obtain ⟨r, hr⟩ := complete c
  refine ⟨r, hr, ?_⟩
  intro s hs; rw [hs] at hr; clear hs
  rw [←CauchySeq.apply_constHom, ←CauchySeq.apply_constHom] at hr
  exact (inj (CauchySeq.constHom (α := ℂ) (γ := ℝ)) hr).symm

noncomputable section

private def lim' (c: CauchySeq.Completion ℂ ℝ) : ℂ := Classical.choose_unique (complete' c)

private def lim'_const (r: ℂ) : lim' (CauchySeq.Completion.const r) = r := by
  have := Classical.choose_unique_spec (complete' (CauchySeq.Completion.const r))
  rw [←CauchySeq.apply_constHom, ←CauchySeq.apply_constHom] at this
  exact (inj (CauchySeq.constHom (α := ℂ) (γ := ℝ)) this).symm

@[irreducible]
def lim : CauchySeq.Completion ℂ ℝ ≃+* ℂ := RingEquiv.symm {
  toFun := CauchySeq.Completion.const
  invFun := lim'
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl
  rightInv := lim'_const
  leftInv c := (Classical.choose_unique_spec (complete' c)).symm
}

unseal lim in
def symm_lim : (lim.symm: _ -> _) = CauchySeq.Completion.const := rfl

@[simp] def lim_const (r: ℝ) : lim (CauchySeq.Completion.const r) = r := by
  rw [←symm_lim, RingEquiv.symm_coe]

@[simp] def const_lim (c: CauchySeq.Completion ℂ ℝ) : CauchySeq.Completion.const (lim c) = c := by
  rw [←symm_lim, RingEquiv.coe_symm]

end

end Complex
