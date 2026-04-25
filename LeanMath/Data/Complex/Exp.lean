import LeanMath.Data.Complex.Cauchy
import LeanMath.Data.Fintype.Algebra.Monoid
import LeanMath.Data.RsqrtD.Char
import LeanMath.Data.Nat.Factorial

variable [LEM]

namespace Complex

variable [FieldOps α] [IsField α] [HasChar α 0]

def exp_sum' (s: α) (n o: ℕ) : α :=
  ∑i: Fin n, (s ^ (o + i.val)) /? ((o + i.val).fact: α)

def exp_sum (s: α) (n: ℕ) : α :=
  exp_sum' s n 0

def exp_sum_eq_exp_sum' (s: α) (n: ℕ) : exp_sum s n = exp_sum' s n 0 := rfl

@[simp] def exp_sum'_zero (f: α) (o: ℕ) : exp_sum' f 0 o = 0:= rfl
@[simp] def exp_sum'_succ (f: α) (n: ℕ) (o: ℕ) : exp_sum' f (n + 1) o =
  f ^ o /? (o.fact: α) + exp_sum' f n (o + 1) := by
  unfold exp_sum'
  rw [fin_sum_succ]
  dsimp; congr 2; ext i
  congr 2
  rw [add_assoc, add_comm 1]
  rw [add_assoc, add_comm 1]

def exp_sum'_sub_exp_sum' (s: α) (i j o: ℕ) (h: j ≤ i) : exp_sum' s i o - exp_sum' s j o = exp_sum' s (i - j) (o + j) := by
  induction i generalizing j o with
  | zero =>
    cases Nat.le_zero.mp h
    simp [exp_sum', sub_zero]
  | succ i ih =>
    cases j with
    | zero => simp [sub_zero]
    | succ j =>
      simp
      rw [add_comm _ (exp_sum' s j _),
        sub_add, add_comm, add_sub_assoc, sub_self,
        add_zero, ih, Nat.succ_add]
      rfl
      apply Nat.le_of_succ_le_succ
      assumption

def exp_sum_sub_exp_sum (s: ComplexRational) (i j: ℕ) (h: j ≤ i) : exp_sum s i - exp_sum s j = exp_sum' s (i - j) j := by
  unfold exp_sum
  rw [exp_sum'_sub_exp_sum', Nat.zero_add]
  assumption

def ratCast_norm (q: ℚ) : ‖(RsqrtD.of_real q: ComplexRational)‖ = ‖q‖ := by
  rw [ComplexRational.norm_def]
  show _ + 0 = _; rw [add_zero]
  rfl

def natCast_norm (n: ℕ) : ‖(n: ComplexRational)‖ = n := by
  rw [ComplexRational.norm_def]
  show _ + 0 = _; rw [add_zero]
  simp
  rw [abs_eq_of_nonneg]
  apply nonneg_natCast

def norm_pow_le_pow_norm (s: ComplexRational) (n: ℕ) : ‖s ^ n‖ ≤ ‖s‖ ^ n := by
  induction n with
  | zero =>
    simp [npow_zero]
    rw [←natCast_one, natCast_norm, natCast_one]
  | succ n ih =>
    rw [npow_succ, npow_succ]
    apply le_trans; apply norm_mul_le_mul_norm
    apply mul_le_mul_of_nonneg_right
    assumption
    apply norm_nonneg

def norm_exp_sum'_le_exp_sum'_norm (s: ComplexRational) : ‖exp_sum' s i o‖ ≤ exp_sum' ‖s‖ i o := by
  induction i generalizing o with
  | zero => simp; rfl
  | succ i ih =>
    simp; apply le_trans
    apply norm_add_le_add_norm
    apply add_le_add
    · rw [div?_eq_mul_inv?]
      apply le_trans
      apply norm_mul_le_mul_norm
      apply le_trans
      apply mul_le_mul_of_nonneg_right
      apply norm_pow_le_pow_norm
      apply norm_nonneg
      apply le_of_eq; congr
      show ‖(RsqrtD.of_real (o.fact: ℚ))⁻¹?~(_)‖ = _
      erw [←map_inv? (RsqrtD.of_real (α := ℚ) (r := (-1: ℤ))) (o.fact: ℚ) (by invert_tactic)]
      rw [ratCast_norm, abs_eq_of_nonneg]
      apply le_of_lt
      apply pos_inv?
      apply lt_of_le_of_ne
      apply nonneg_natCast
      symm; invert_tactic
    · apply ih

def norm_exp_sum_le_exp_sum_norm (s: ComplexRational) : ‖exp_sum s i‖ ≤ exp_sum ‖s‖ i :=
  norm_exp_sum'_le_exp_sum'_norm s

def rat_eqv_exp (a: ComplexRational) : is_cauchy_eqv (fun i => exp_sum a i) (fun i => exp_sum a i) := by
  intro ε εpos
  dsimp
  have ⟨n, hn⟩ := archimedean_iff_nat_lt.mp inferInstance ε⁻¹?
  apply CauchySeq.Eventually₂_of_le
  refine ⟨?_⟩; intro i j ; rw [norm_sub]; exact id
  have k := 0
  exists k; intro i j hi hj h
  rw [norm_sub, exp_sum_sub_exp_sum _ _ _ h]
  apply lt_of_le_of_lt
  apply norm_exp_sum'_le_exp_sum'_norm
  sorry

def eqv_exp (a b: CauchySeq ComplexRational ℚ) (h: a ≈ b) : is_cauchy_eqv (fun i => exp_sum (a i) i) (fun i => exp_sum (b i) i) := by
  intro ε εpos
  dsimp
  have ⟨n, hn⟩ := archimedean_iff_nat_lt.mp inferInstance ε⁻¹?
  have : n ≠ 0 := by
    intro rfl;
    rw [natCast_zero] at hn
    exact Relation.asymm hn (pos_inv? _ εpos)
  replace hn : (n: ℚ)⁻¹? < _ := inv?_lt_inv? (pos_inv? _ εpos) hn
  rw [inv?_inv?] at hn
  have k := n
  exists k; intro i j hi hj
  rcases le_total i j with h | h
  · sorry
  · sorry

-- def exp' (s: CauchySeq ComplexRational ℚ) : CauchySeq ComplexRational ℚ where
--   toFun i := exp_sum (s i) i
--   is_cauchy' := by
--     apply eqv_exp
--     rfl

-- def exp (s: ℂ) : ℂ :=
--   CauchySeq.lift (fun s => Complex.equivCauchy.symm (exp' s).ofSeq) (by
--     intro a b h
--     dsimp; congr 1; apply CauchySeq.sound
--     apply eqv_exp
--     assumption) (Complex.equivCauchy s)

end Complex
