import LeanMath.Data.Real.Lattice

variable [LEM]

namespace Rational

def sqrt_approx (q: ℚ) (n: ℕ) : ℚ :=
  if 0 ≤ q then
    Fin.foldr n (fun _ x =>
      if h:x = 0 then
        0
      else
        (x + q /? x) /? 2
    ) 1
  else
    0

@[simp] def sqrt_approx_neg (q: ℚ) (hq: q < 0): sqrt_approx q i = 0 := by
  unfold sqrt_approx
  rw [if_neg]; apply not_le.mpr
  assumption

@[simp] def sqrt_approx_zero (q: ℚ) (hq: 0 ≤ q): sqrt_approx q 0 = 1 := by
  unfold sqrt_approx
  rw [if_pos hq]; rfl

def sqrt_approx_pos (q: ℚ) (hq: 0 ≤ q) (i: ℕ) : 0 < sqrt_approx q i := by
  unfold sqrt_approx
  rw [if_pos hq]
  induction i with
  | zero =>
    rw [Fin.foldr_zero]
    decide +kernel
  | succ n ih =>
    rw [Fin.foldr_succ]
    rw [dif_neg]; apply pos_div?_natCast
    rw (occs := [1]) [←add_zero 0]
    apply add_lt_add_of_lt_of_le
    assumption
    rcases lt_or_eq_of_le hq with hq | hq
    apply le_of_lt; apply pos_div?
    assumption
    assumption
    subst q; rw [div?_eq_mul_inv?, zero_mul]
    apply ne_of_gt
    assumption

def sqrt_approx_ne_zero (q: ℚ) (hq: 0 ≤ q) : sqrt_approx q i ≠ 0 := by
  apply ne_of_gt; apply sqrt_approx_pos
  assumption

@[simp] def sqrt_approx_succ (i: ℕ) (q: ℚ) (hq: 0 ≤ q): sqrt_approx q (i + 1) = (sqrt_approx q i + q /? sqrt_approx q i~(by exact ne_of_gt (sqrt_approx_pos q hq i))) /? 2 := by
 rw [sqrt_approx, if_pos hq, Fin.foldr_succ, dif_neg]
 unfold sqrt_approx
 split; rfl
 contradiction
 have := sqrt_approx_ne_zero q (i := i) hq
 unfold sqrt_approx at this
 rwa [if_pos hq] at this

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply sqrt_approx_go_ne_zero <;> invert_tactic)

private def sqrt_den_ne_zero' (hq: 0 ≤ q) : 2 * sqrt_approx q i ≠ 0 := by
    show ((2: ℕ): ℚ) * _ ≠ 0
    apply ne_of_gt
    apply pos_mul_of_pos
    decide +kernel
    apply sqrt_approx_pos
    assumption

private def sqrt_den_ne_zero (hq: 0 ≤ q) : (2 * sqrt_approx q i) ^ 2 ≠ 0 := by
    refine npow_ne_zero ?_
    apply sqrt_den_ne_zero'
    assumption

def sqrt_approx_err_spec (q: ℚ) (i: ℕ) (hq: 0 ≤ q) : sqrt_approx q (i + 1) ^ 2 - q = (sqrt_approx q i ^ 2 - q) ^ 2 /? (2 * sqrt_approx q i) ^ 2~(by
    apply sqrt_den_ne_zero
    assumption) := by
    rw [sqrt_approx_succ _ _ hq]
    let Q := q.sqrt_approx i
    show ((Q + _ /? Q ~(_)) /? _ ~(_)) ^ _ - _ = (Q ^ 2 - _) ^ 2 /? (2 * Q) ^ 2 ~(_)
    apply of_mul_right₀
    show (2 * Q) ^ 2 ≠ 0
    apply sqrt_den_ne_zero
    assumption
    rw [sub_mul, div?_mul_cancel]
    rw [add_div?, div?_div?, add_sq,
      ←mul_assoc, mul_comm ((2: ℕ): ℚ), show ((2: ℕ): ℚ) = 2 from rfl,
      div?_mul_cancel, ←mul_div?_assoc,
      add_mul, npow_div? q, div?_mul_cancel,
      add_mul, npow_two (2 * Q), ←mul_assoc ((Q * q) /? _~(_)),
      div?_mul_cancel, ←npow_two, ←mul_npow, ←mul_assoc,
      div?_mul_cancel, sub_sq, ←npow_two]
    rw [add_sub_assoc, add_assoc, sub_add_assoc]
    congr 1
    rw [←add_sub_assoc, add_comm, add_sub_assoc, add_comm _ (q ^ 2)]
    congr
    rw [show ((2: ℕ): ℚ) = 2 from rfl, mul_npow]
    apply eq_neg_of_add
    rw [mul_comm Q, mul_assoc, mul_left_comm Q, ←npow_two, mul_left_comm,
      mul_left_comm q, mul_comm _ q, ←sub_mul, ←add_mul]
    rw [show (2 - 2 ^ 2 + 2: ℚ) = 0 from ?_, zero_mul]
    decide +kernel

-- def sqrt_approx_step_monotone {a b c d: ℚ} (h₀: a ≤ c) (h₁: b ≤ d) (hb: b ≠ 0) (hd: d ≠ 0) :
--   (b + a /? b) /? 2 ≤ (d + c /? d) /? 2 := by
--   rw [div?_eq_mul_inv?, div?_eq_mul_inv? _ 2]
--   apply mul_le_mul_of_nonneg_right
--   apply add_le_add
--   assumption
--   rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
--   apply le_trans
--   apply mul_le_mul_of_nonneg_right
--   assumption
--   · sorry
--   apply mul_le_mul_of_nonneg_left
--   · sorry
--   · sorry
--   · decide +kernel

def nonneg_sq (q: ℚ) : 0 ≤ q ^ 2 := by
  rcases le_total 0 q
  rw [npow_two, ←mul_zero q]
  apply mul_le_mul_of_nonneg_left
  assumption
  assumption
  rw [←neg_sq, npow_two, ←mul_zero (-q)]
  have : 0 ≤ -q := by
    rw [←neg_zero]; apply neg_le_neg
    assumption
  apply mul_le_mul_of_nonneg_left
  assumption
  assumption

def le_sqrt_approx_sq (q: ℚ) (i: ℕ) (hi: 0 < i) : q ≤ (sqrt_approx q i) ^ 2 := by
  match i with
  | i + 1 =>
  by_cases hq:q < 0
  rw [sqrt_approx_neg _ hq, zero_npow]
  apply le_of_lt; assumption
  decide +kernel
  replace hq := not_lt.mp hq
  rename_i j; clear j hi
  apply le_of_add_le_add_right
  rw [add_neg_cancel, ←sub_eq_add_neg, sqrt_approx_err_spec _ _ hq]
  rw [←npow_div? _ _ (sqrt_den_ne_zero' hq)]
  apply nonneg_sq

def sqrt_approx_monotone (i: ℕ) : Monotone (sqrt_approx · i) := by
  intro a b h; dsimp
  by_cases hb:b < 0
  · rw [sqrt_approx_neg, sqrt_approx_neg]
    assumption
    apply lt_of_le_of_lt
    assumption
    assumption
  replace hb := not_lt.mp hb
  by_cases ha:a < 0
  · rw [sqrt_approx_neg]
    apply le_of_lt
    apply sqrt_approx_pos
    assumption
    assumption
  replace ha := not_lt.mp ha
  -- repalce ha
  -- rcases Or.symm (lt_or_eq_of_le ha) with ha | ha
  -- sorry
  -- replace hb := lt_of_lt_of_le ha h
  induction i with
  | zero =>
    rw [sqrt_approx_zero, sqrt_approx_zero]
    assumption
    assumption
  | succ i ih =>
    let A := a.sqrt_approx i
    let B := b.sqrt_approx i
    let δ := B - A
    have B_eq_A_add_δ : B = A + δ := by
      unfold δ
      rw [add_comm, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
    have : 0 ≤ δ := by
      unfold δ
      rw [sub_eq_add_neg]
      apply le_of_add_le_add_right
      rwa [add_assoc, neg_add_cancel, add_zero, zero_add]
    rw [sqrt_approx_succ _ _ (by assumption), sqrt_approx_succ _ _ (by assumption),
      div?_eq_mul_inv?, div?_eq_mul_inv?]
    apply mul_le_mul_of_nonneg_right _ _ (by decide +kernel)
    have : 0 < 2 * (A * B) := by
      apply pos_mul_of_pos
      decide +kernel
      apply pos_mul_of_pos
      apply sqrt_approx_pos
      assumption
      apply sqrt_approx_pos
      assumption
    show A + a /? A~(_) ≤ B + b /? B~(_)
    cases i with
    | zero =>
      unfold A B
      clear this; clear this B_eq_A_add_δ δ A B
      unfold sqrt_approx
      simp [ha, hb]
      rw [div?_one, div?_one]
      apply add_le_add_left
      assumption
    | succ i =>
      apply le_of_add_le_add_right
      rw [add_neg_cancel, neg_add_rev, add_comm _ (-A),
        add_assoc, add_left_comm _ (-A), ←add_assoc, ←sub_eq_add_neg]
      show 0 ≤ δ + (b /? B~(_) + -(a /? A~(_)))
      apply le_of_mul_le_mul_of_pos_left _ _ _ this
      rw [mul_zero, mul_add, mul_add,
        mul_assoc _ _ (_ /? _~(_)),
        mul_assoc _ _ (_ /? _~(_)),
        ←neg_mul_right,
        mul_assoc _ _ (_ /? _~(_)),
        mul_assoc _ _ (_ /? _~(_)),
        mul_left_comm A B (a /? _~(_)),
        mul_comm B, div?_mul_cancel,
        mul_comm A (_ /? _~(_)), div?_mul_cancel,
        ←sub_eq_add_neg, ←mul_sub, mul_assoc,
        ←mul_add, ←mul_zero 2]
      apply mul_le_mul_of_nonneg_left _ _ (by decide +kernel)
      rw [mul_sub, mul_assoc, ←npow_two, mul_comm A B, mul_assoc,
        ←npow_two, sub_add_assoc, sub_eq_add_neg,
        add_left_comm _ (A * b),
        ←neg_add_rev, add_comm (B * a),
        ←add_assoc, ←mul_add, ←mul_add]
      rw [B_eq_A_add_δ, add_sq]
      simp [add_mul, mul_add, neg_add_rev]
      rw [show A * A ^ 2  = A ^ 3 by rw [mul_comm A, npow_succ _ 2]]
      rw [mul_comm δ]
      rw [mul_left_comm, ←mul_assoc A, ←npow_two,
        mul_comm δ]
      rw [
        show A ^ 3 + Nat.cast 2 * (A ^ 2 * δ) + A * δ ^ 2 + A * b + (-(a * δ) + -(A * a) + (-(A ^ 2 * δ) + -A ^ 3)) =
          A ^ 3 + -A ^ 3 + (Nat.cast 2 * (A ^ 2 * δ) + (-(A ^ 2 * δ))) +
          -(a * δ) + A * δ ^ 2 + (A * b + -(A * a)) by ac_rfl
      ]
      rw [add_neg_cancel, zero_add, two_mul, add_assoc (A ^ 2 * δ), add_neg_cancel, add_zero]
      rw [←sub_eq_add_neg (A * b), ←mul_sub, ←sub_eq_add_neg, ←sub_mul]
      rw [←add_zero 0]; apply add_le_add
      rw [←add_zero 0]; apply add_le_add
      rw [←zero_mul δ]; apply mul_le_mul_of_nonneg_right
      apply le_sub_iff_add_le.mpr
      rw [zero_add]; apply le_sqrt_approx_sq
      apply Nat.zero_lt_succ
      assumption
      rw [←zero_mul (δ^2)]; apply mul_le_mul_of_nonneg_right
      apply le_of_lt; apply sqrt_approx_pos
      assumption
      apply nonneg_sq
      rw [←zero_mul (b - a)]; apply mul_le_mul_of_nonneg_right
      apply le_of_lt; apply sqrt_approx_pos
      assumption
      apply le_sub_iff_add_le.mpr
      rw [zero_add]
      assumption

def sqrt_approx_nonneg (i: ℕ) : 0 ≤ sqrt_approx a i := by
  rcases lt_or_le a 0 with _ | ha
  rwa [sqrt_approx_neg]
  apply le_of_lt; apply sqrt_approx_pos
  assumption

def sqrt_approx_lower_bound (a b q: ℚ) (hq: 0 ≤ q) (ha: a ≤ q) (hb: q ≤ b) :
  (1 /? 2) ⊓ (a /? 2) < sqrt_approx q i := by
  induction i with
  | zero =>
    rw [sqrt_approx_zero _ hq]
    apply lt_of_le_of_lt
    apply min_le_left
    decide
  | succ i ih =>
    rw [sqrt_approx_succ _ _ hq]
    apply lt_of_mul_lt_mul_of_pos_right
    apply pos_natCast 1
    show _ * _ < _ * 2
    dsimp; rw [div?_mul_cancel]
    rw [mul_comm, two_mul]
    apply add_lt_add
    apply ih
    apply lt_of_mul_lt_mul_of_pos_right
    apply sqrt_approx_pos _ hq i
    rw [div?_mul_cancel]
    sorry

-- def q: ℚ := 1 /? 1000000
-- def a := q
-- def b := q
-- def s: ℚ := (1 /? 2) ⊓ (a /? 2)

-- #eval 0 < s ^ 2
-- #eval s ^ 2 < a
-- #eval s < 1
-- #eval 0 < a
-- #eval a ≤ q
-- #eval q ≤ b

-- #eval s * Rational.sqrt_approx q 0 < q
-- #eval s * Rational.sqrt_approx q 0 < q
-- #eval s * Rational.sqrt_approx q 1 < q
-- #eval s * Rational.sqrt_approx q 2 < q
-- #eval s * Rational.sqrt_approx q 3 < q
-- #eval s * Rational.sqrt_approx q 4 < q

-- def sqrt_approx_lower_bound (a b q: ℚ) (hq: 0 ≤ q) (ha: a ≤ q) (hb: q ≤ b) :
--   1 ⊓ (a /? 2) < sqrt_approx q i ∧
--   sqrt_approx q i ≤ 1 ⊔ ((1 + b) /? 2) := by
--   induction i with
--   | zero =>
--     rw [sqrt_approx_zero _ hq]
--     apply And.intro
--     apply lt_of_le_of_lt min_le_left
--     decide +kernel
--     apply left_le_max
--   | succ i ih =>
--     sorry

-- #print axioms sqrt_approx_monotone

def sqrt_approx_uniform_continuous {q: ℚ}
   : is_cauchy_eqv (Rational.sqrt_approx q) (Rational.sqrt_approx q) := by
  intro ε εpos
  show CauchySeq.Eventually₂ fun i j => ‖Rational.sqrt_approx q i - Rational.sqrt_approx q j‖ < ε
  rcases lt_or_le q 0 with hq | hq
  · simp [sqrt_approx_neg _ hq, sub_zero]
    exists 0; intros; assumption
  have a := ε
  let s: ℚ := 1 ⊓ (a /? ((2: ℕ): ℚ))
  sorry

end Rational

namespace Real

def sqrt_func (f: CauchySeq ℚ ℚ) (i: ℕ) : ℚ := (f i).sqrt_approx i

def sqrt_func_is_cauchy_of_const {q: ℚ}
   : is_cauchy_eqv (sqrt_func (CauchySeq.const q)) (sqrt_func (CauchySeq.const q)) := by
  intro ε εpos
  show CauchySeq.Eventually₂ fun i j => ‖Rational.sqrt_approx q i - Rational.sqrt_approx q j‖ < ε

  sorry

-- def sqrt_func_is_cauchy_of_pos {f g: CauchySeq ℚ ℚ} (h: f ≈ g)
--   (hf: CauchySeq.IsPos f)
--   (hg: CauchySeq.IsPos g) : is_cauchy_eqv (sqrt_func f) (sqrt_func g) := by
--   intro ε εpos
--   sorry

-- def sqrt_func_is_cauchy_of_eq_zero' {f: CauchySeq ℚ ℚ} (hf: f ≈ 0)
--    : is_cauchy_eqv (sqrt_func f) (fun _ => 0) := by
--   intro ε εpos
--   have ε2_pos : 0 < (ε /? 2) ^ 2 := by
--     rw (occs := [1]) [npow_two, ←mul_zero (ε /? 2)];
--     apply mul_lt_mul_of_pos_left
--     apply pos_div?_natCast
--     assumption
--     apply pos_div?_natCast
--     assumption
--   have ⟨k, hk⟩ := hf ((ε /? 2) ^ 2) ε2_pos
--   exists k; intro i j hi hj
--   dsimp; rw [sub_zero]
--   dsimp at hk
--   replace hk (i: ℕ) (hi: k ≤ i) : ‖f i‖ < (ε /? 2) ^ 2 := by
--     have := hk i i hi hi
--     have : ‖f i - 0‖ < _ := this
--     rwa [sub_zero] at this
--   unfold sqrt_func
--   apply lt_of_le_of_lt
--   show ‖_‖ ≤ ‖Rational.sqrt_approx ((ε /? 2) ^ 2) i‖
--   rw [abs_eq_of_nonneg, abs_eq_of_nonneg]
--   apply Rational.sqrt_approx_monotone
--   apply le_trans
--   show f i ≤ ‖f i‖
--   rw [abs_eq_max]; apply left_le_max
--   apply le_of_lt
--   apply hk
--   assumption
--   apply Rational.sqrt_approx_nonneg
--   apply Rational.sqrt_approx_nonneg
--   rw (occs:= [2]) [←half_add_half ε]
--   rw [←two_mul]; generalize ε /? 2 = ε
--   clear hk hj hi k j hf f
--   -- induction i with
--   -- | zero =>
--   --   rw [Rational.sqrt_approx_zero, abs_one]
--   --   sorry
--   -- | succ i ih =>
--   --   sorry

--   -- apply Rational.le_sqrt_approx_sq


--   -- replace hk : ‖f i - 0‖ < _ := hk i j hi hj
--   -- simp [sub_zero] at *
--   -- unfold sqrt_func
--   -- by_cases h₀:f i < 0
--   -- rwa [Rational.sqrt_approx_neg, norm_zero]
--   -- assumption
--   -- replace h₀ := not_lt.mp h₀
--   sorry

-- def sqrt_func_is_cauchy_of_eq_zero {f g: CauchySeq ℚ ℚ} (hf: f ≈ 0) (hg: g ≈ 0)
--    : is_cauchy_eqv (sqrt_func f) (sqrt_func g) := by
--   apply CauchySeq.trans (b := fun _ => 0)
--   apply (CauchySeq.const _).is_cauchy
--   apply sqrt_func_is_cauchy_of_eq_zero' hf
--   apply CauchySeq.symm
--   apply sqrt_func_is_cauchy_of_eq_zero' hg

-- def sqrt_func_is_cauchy {f g: CauchySeq ℚ ℚ} (h: f ≈ g) : is_cauchy_eqv (sqrt_func f) (sqrt_func g) := by
--   rcases em (f ≈ 0) with hf | hf
--   · have hg := CauchySeq.setoid.trans (CauchySeq.setoid.symm h) hf
--     apply sqrt_func_is_cauchy_of_eq_zero
--     assumption
--     assumption
--   have := (CauchySeq.norm_pos_of_ne_zero _ hf)
--   rcases CauchySeq.of_norm_pos _ this with hf | hf
--   · have hg := (CauchySeq.is_cauchy_eqv.IsPos _ _ h).mp hf
--     apply sqrt_func_is_cauchy_of_pos
--     assumption
--     assumption
--     assumption
--   · have := is_cauchy_eqv.neg h
--     have hg := (CauchySeq.is_cauchy_eqv.IsPos (-f) (-g) this).mp hf
--     obtain ⟨B₀, hB₀, hf⟩ := hf
--     obtain ⟨B₁, hB₁, hg⟩ := hg
--     have ⟨k, hk⟩ := hf.merge hg
--     intro ε εpos
--     exists k; intro i j hi hj
--     have ⟨hai, hbi⟩ := hk i hi
--     have ⟨haj, hbj⟩ := hk j hj
--     unfold sqrt_func
--     rwa [Rational.sqrt_approx_neg, Rational.sqrt_approx_neg, sub_zero, norm_zero]
--     rw [←neg_lt_neg_iff, neg_zero]
--     apply flip lt_trans <;> assumption
--     rw [←neg_lt_neg_iff, neg_zero]
--     apply flip lt_trans <;> assumption

-- def computable_sqrt : ℝ -> ℝ :=
--   Real.lift (fun q => Real.ringEquivCauchySeq.symm <| CauchySeq.ofSeq <| {
--     toFun := sqrt_func q
--     is_cauchy' := by apply sqrt_func_is_cauchy; rfl
--   }) <| by
--     intro a b h
--     apply sound
--     apply sqrt_func_is_cauchy
--     assumption

-- open Classical Real.Repr.Float  in
-- #eval! (computable_sqrt <| Real.ofRat (1 /? 2: ℚ)).offset 3

-- def sqrt_eqv (s: CauchySeq ℚ ℚ) (r: ℝ) (h: r = Real.equivCauchySeq.symm s.ofSeq) :
--   is_cauchy_eqv (fun i => (sqrt_func s i: ℝ)) fun x => r.sqrt := by
--   rcases lt_trichotomy r 0 with rneg | rfl | rpos
--   · let r' := CauchySeq.Completion.const r
--     let s' := castCauchy s.ofSeq
--     have : r' = s' := by unfold r' s'; rw [h, castCauchy_eq]; rfl
--     replace h := CauchySeq.exact this; clear this
--     intro ε εpos; dsimp; clear r' s'
--     sorry
--   · simp
--     sorry
--   · let r' := CauchySeq.Completion.const r
--     let s' := castCauchy s.ofSeq
--     have : r' = s' := by unfold r' s'; rw [h, castCauchy_eq]; rfl
--     replace h := CauchySeq.exact this; clear this
--     intro ε εpos; dsimp; clear r' s'
--     sorry

-- def sqrt' (r: ℝ) : ℝ := r.lift_with (fun s hs => Real.of_seq_converges_to (fun i => sqrt_func s i) ⟨r.sqrt, by
--   apply sqrt_eqv
--   assumption⟩) (by
--     intro a b ha hb
--     dsimp
--     rw [of_seq_converges_to_eq _ r.sqrt, of_seq_converges_to_eq _ r.sqrt]
--     apply sqrt_eqv; assumption
--     apply sqrt_eqv; assumption)

end Real
