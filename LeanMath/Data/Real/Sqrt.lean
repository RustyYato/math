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

def sqrt_approx_err (q: ℚ) (i: ℕ) (hq: 0 ≤ q) := (sqrt_approx q i ^ 2 - q) ^ 2 /? (2 * sqrt_approx q i) ^ 2~(by
  apply sqrt_den_ne_zero
  assumption)

def nonneg_sqrt_approx_err (q: ℚ) (i: ℕ) (hq: 0 ≤ q) : 0 ≤ sqrt_approx_err q i hq := by
  unfold sqrt_approx_err
  rw [div?_eq_mul_inv?]
  apply nonneg_mul
  apply nonneg_sq
  apply le_of_lt
  apply pos_inv?
  apply lt_of_le_of_ne
  apply nonneg_sq
  symm; apply sqrt_den_ne_zero
  assumption

def sqrt_approx_err_init (lb ub: ℚ) (hlb: 0 < lb) : ℚ := ((1 - lb) ^ 2 ⊔ (1 - ub) ^ 2) /? (4: ℕ)

def sqrt_approx_err_antitone (q: ℚ) (hq: 0 ≤ q) : Antitone (sqrt_approx_err q . hq) := by
  sorry

def sqrt_approx_err_le (lb ub q: ℚ) (i: ℕ) (hlb: 0 < lb) (hq: lb ≤ q) (hub: q ≤ ub) : sqrt_approx_err q i (le_trans (le_of_lt hlb) hq) ≤ 4 * lb * (sqrt_approx_err_init lb ub hlb /? (4 * lb)) ^ (2 ^ (i - 1)) := by
  have nonneg_q := le_trans (le_of_lt hlb) hq
  have : (1 - q) ^ 2 ≤ (1 - lb) ^ 2 ⊔ (1 - ub) ^ 2 := ?_
  · induction i with
    | zero =>
      simp [npow_one, sqrt_approx_err, sqrt_approx, nonneg_q,
        mul_one, show (2 ^ 2: ℚ) = 4 from rfl,
        sqrt_approx_err_init]
      rw [mul_comm (4 * lb), div?_mul_cancel]
      rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
      apply mul_le_mul_of_nonneg_right
      · rw [one_npow]
        rcases le_total ((1 - q)^2) ((1 - lb)^2) with h₀ | h₀
        · apply le_trans h₀
          apply left_le_max
        rcases le_total ((1 - q)^2) ((1 - ub)^2) with h₁ | h₁
        · apply le_trans h₁
          apply right_le_max
        · assumption
      · show 0 ≤ ((4: ℕ)⁻¹?: ℚ)
        decide
    | succ i ih =>
      simp
      cases i with
      | zero =>
        apply le_trans
        apply sqrt_approx_err_antitone
        apply zero_le_one
        simp [npow_one]; clear ih
        simp [sqrt_approx_err_init]
        rw [mul_comm (4 * lb), div?_mul_cancel]
        simp [sqrt_approx_err, sqrt_approx, nonneg_q, one_npow,
          mul_one]
        rw [div?_eq_mul_inv?, div?_eq_mul_inv? _ ((4: ℕ): ℚ)]
        apply mul_le_mul_of_nonneg_right _ _ (by
          show 0 ≤ (4: ℚ)⁻¹?
          decide)
        assumption
      | succ i =>
        dsimp at ih

        sorry
  · sorry
def sqrt_approx_err_spec (q: ℚ) (i: ℕ) (hq: 0 ≤ q) : sqrt_approx q (i + 1) ^ 2 - q = sqrt_approx_err q i hq := by
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
  unfold sqrt_approx_err
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

noncomputable def sqrt_set (r: ℝ) : Set ℝ where
  Mem x := x ^ 2 ≤ ‖r‖

def mem_sqrt_set (r: ℝ) : ∀{x}, x ∈ sqrt_set r ↔ x ^ 2 ≤ ‖r‖ := Iff.rfl

@[implicit_reducible]
def sqrt_set_nonempty (r: ℝ) : (sqrt_set r).Nonempty := by
  exists 0;
  unfold sqrt_set; dsimp
  rw [zero_npow]; apply norm_nonneg
  decide

@[implicit_reducible]
def sqrt_set_bounded (r: ℝ) : (sqrt_set r).BoundedAbove := by
  exists 1 ⊔ ‖r‖
  intro x hx
  replace hx : x ^ 2 ≤ ‖r‖ := hx
  rcases le_total 1 ‖r‖ with h | h
  · rw [max_eq_right h]
    rcases Or.symm (lt_or_le 1 x) with hx' | hx'
    apply le_trans hx'; assumption
    rw [←not_lt]
    intro g
    have := mul_lt_mul₀ ?_ ?_ g hx'
    rw [mul_one, ←npow_two] at this
    exact not_le_of_lt this hx
    apply lt_of_lt_of_le _ h
    apply zero_lt_one
    apply lt_trans _ hx'
    apply zero_lt_one
  · rw [max_eq_left h]
    replace hx := le_trans hx h
    rcases Or.symm (lt_or_le 0 x) with hx' | hx'
    apply le_trans hx'; apply zero_le_one
    rw [←not_lt]; intro g
    have := mul_lt_mul₀ ?_ ?_ g g
    rw [mul_one, ←npow_two] at this
    exact not_le_of_lt this hx
    apply zero_lt_one
    assumption


noncomputable def sqrt (r: ℝ) : ℝ := ⨆ (sqrt_set r)

@[simp]
def sqrt_sq (r: ℝ) : sqrt (r ^ 2) = ‖r‖ := by
  apply le_antisymm
  · apply csSup_le
    apply sqrt_set_nonempty
    intro x hx
    replace hx : x ^ 2 ≤ ‖r ^ 2‖ := hx
    rcases em (r = 0) with rfl | h
    rw [zero_npow, norm_zero] at hx
    rw [norm_zero]
    · rw [←not_lt]
      intro h
      have := mul_lt_mul₀_of_le_of_lt (le_refl _) h (le_of_lt h) h
      rw [mul_zero, ←npow_two] at this
      exact not_le_of_lt this hx
    decide
    rw [←not_lt]; intro h
    have := mul_lt_mul₀ ?_ ?_ h h
    rw [←norm_mul, ←npow_two, ←npow_two] at this
    exact not_le_of_lt this hx
    apply lt_of_le_of_ne
    apply norm_nonneg
    intro g
    have := of_norm_eq_zero g.symm
    contradiction
    apply lt_of_le_of_lt _ h
    apply norm_nonneg
  · apply le_csSup
    apply sqrt_set_bounded
    show ‖r‖ ^ 2 ≤ _
    rw [npow_two, ←norm_mul,  ←npow_two]

def nonneg_sqrt (r: ℝ) : 0 ≤ sqrt r := by
  apply le_csSup
  apply sqrt_set_bounded
  show _ ≤ ‖r‖
  rw [npow_two, mul_zero]
  apply norm_nonneg

@[simp]
def sq_sqrt (r: ℝ) : (sqrt r) ^ 2 = ‖r‖ := by
  apply le_antisymm
  · rw [←not_lt]; intro h
    have _ : 0 < r.sqrt := by
      apply lt_of_le_of_ne
      apply nonneg_sqrt
      symm; intro g
      rw [g, npow_two, mul_zero] at h
      exact not_le.mpr h (norm_nonneg _)
    let _ : 0 < (2: ℕ) * r.sqrt := by
      apply pos_mul_of_pos
      apply pos_natCast
      assumption
    let ε := (r.sqrt ^ 2 - ‖r‖) /? ((2: ℕ) * r.sqrt)
    have εpos : 0 < ε := by
      unfold ε
      apply pos_div?
      rw [lt_sub_iff_add_lt, zero_add]
      assumption
      apply mul_pos
      apply pos_natCast
      assumption
    have pos_rsqrt_sub_ε : 0 < r.sqrt - ε := by
      rw [←mul_one r.sqrt, ←div?_self ((2: ℕ) * r.sqrt)]
      unfold ε
      rw [←mul_div?_assoc, ←sub_div?]
      apply pos_div?
      · rw [sub_eq_add_neg _ ‖r‖, sub_add, sub_eq_add_neg _ (-‖r‖), neg_neg,
          mul_comm, mul_assoc, npow_two, add_comm,
          two_mul, add_sub_assoc,add_sub_assoc, sub_self,
            add_zero, add_comm, lt_add_iff_sub_lt, zero_sub,
            ←npow_two]
        apply lt_of_le_of_lt
        show -‖r‖ ≤ ‖r‖
        refine neg_le_of_nonneg ?_
        apply norm_nonneg
        assumption
      · assumption
      · apply ne_of_gt
        assumption
    have ⟨x, hx, lt_x⟩ := lt_mem_of_lt_csSup _ (sqrt_set_nonempty r) (a := r.sqrt - ε) (by
      show r.sqrt - ε < r.sqrt
      rw [sub_eq_add_neg]
      rw (occs := [2]) [←add_zero r.sqrt]
      apply add_lt_add_left
      rwa [←neg_lt_neg_iff, neg_neg, neg_zero])
    have upos := lt_trans pos_rsqrt_sub_ε lt_x
    have := mul_lt_mul₀ ?_ ?_ lt_x lt_x
    rw [←npow_two, ←npow_two, sub_sq] at this
    rw [←mul_assoc, mul_comm, div?_mul_cancel,
      sub_eq_add_neg _ (_ - _), neg_sub,
      add_comm (r.sqrt ^ 2), sub_add_assoc,
      neg_add_cancel, add_zero] at this
    have := lt_of_le_of_lt (a := ‖r‖) ?_ this
    apply not_le_of_lt this
    assumption
    rw (occs := [1]) [←add_zero ‖r‖]
    apply add_le_add_left
    · rw [npow_two]
      apply le_of_lt
      apply mul_pos
      assumption
      assumption
    assumption
    assumption
  · rw [←not_lt]; intro h
    let ε := ‖r‖ - r.sqrt ^ 2
    have : 0 < r.sqrt := by
      rw [←not_le]; intro g
      have := le_antisymm g (nonneg_sqrt r)
      rw [this, zero_npow _ (by decide)] at h
      have : ∃x, 0 < x ∧ x ∈ sqrt_set r := by
        exists 1 ⊓ ‖r‖
        apply And.intro
        · rcases min_eq 1 ‖r‖ with h₀ | h₀
          rw [h₀]; apply zero_lt_one
          rwa [h₀]
        rw [mem_sqrt_set]
        rcases le_total 1 ‖r‖ with h₀ | h₀
        rwa [min_eq_left h₀, one_npow]
        rw [min_eq_right]
        rw [←not_lt]; intro g
        have := mul_lt_mul₀_of_le_of_lt ?_ ?_ h₀ g
        rw [←npow_two, one_mul] at this
        exact Relation.irrefl this
        apply norm_nonneg
        apply zero_lt_one
        assumption
      obtain ⟨x, xpos, hx⟩ := this
      have := lt_of_lt_of_le xpos (le_csSup (sqrt_set_bounded _) hx)
      exact not_le_of_lt this g
    have ε_pos : 0 < ε := by rwa [lt_sub_iff_add_lt, zero_add]
    have _ : 0 < (2: ℕ) * r.sqrt + 1 := by
      apply pos_add
      apply pos_mul_of_pos
      apply pos_natCast
      assumption
      apply zero_lt_one
    let δ := 1 ⊓ (ε /? ((2: ℕ) * r.sqrt + 1))
    have δ_mem : δ ∈ Set.Ioc 0 1 := by
      apply And.intro
      · apply lt_min
        apply zero_lt_one
        apply pos_div?
        assumption
        apply pos_add
        apply mul_pos
        apply pos_natCast
        assumption
        apply zero_lt_one
      · apply min_le_left
    have : (r.sqrt + δ) ∈ sqrt_set r := by
      rw [mem_sqrt_set]
      apply le_trans (b := r.sqrt ^ 2 + (2: ℕ) * r.sqrt * δ + δ)
      rw [add_sq, add_assoc, add_assoc]
      apply add_le_add_left
      rw [mul_assoc]
      apply add_le_add_left
      obtain ⟨δ_pos, δ_le_one⟩ := δ_mem
      rw [←not_lt]; intro h
      have := mul_le_mul₀ (le_of_lt δ_pos) (le_of_lt δ_pos) δ_le_one (le_refl δ)
      rw [←npow_two, one_mul] at this
      apply not_le_of_lt h
      assumption
      let δ' := (ε /? ((2: ℕ) * r.sqrt + 1))
      apply le_trans
      show _ ≤ r.sqrt ^ 2 + (2: ℕ) * r.sqrt * δ' + δ'
      · rw [add_assoc, add_assoc]
        apply add_le_add_left
        apply add_le_add
        apply mul_le_mul_of_nonneg_left
        apply min_le_right
        apply le_of_lt; apply mul_pos
        apply pos_natCast
        assumption
        apply min_le_right
      rw (occs := [2]) [←one_mul δ']
      rw [add_assoc, ←add_mul, mul_comm, div?_mul_cancel,
        add_comm, sub_add_assoc, neg_add_cancel, add_zero]
    have : r.sqrt + δ ≤ r.sqrt := le_csSup (sqrt_set_bounded _) this
    apply not_lt.mpr this
    rw (occs := [1]) [←add_zero r.sqrt]
    apply add_lt_add_left
    exact δ_mem.left

def sqrt_mono : Monotone (α := { x: ℝ // 0 ≤ x }) (fun x => x.val.sqrt) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  replace h : a ≤ b := h
  dsimp
  apply le_csSup
  apply sqrt_set_bounded
  rwa [mem_sqrt_set, sq_sqrt, abs_eq_of_nonneg, abs_eq_of_nonneg]
  assumption
  assumption

def sqrt_strictMono : StrictMonotone (α := { x: ℝ // 0 ≤ x }) (fun x => x.val.sqrt) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  replace h : a < b := h
  dsimp; apply lt_of_le_of_ne
  apply sqrt_mono (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  apply le_of_lt; assumption
  intro eq
  have : a.sqrt ^ 2 = b.sqrt ^ 2 := by rw [eq]
  rw [sq_sqrt, sq_sqrt, abs_eq_of_nonneg _ ha,
    abs_eq_of_nonneg _ hb] at this
  subst b
  have := Relation.irrefl h
  contradiction

@[simp]
def sqrt_neg (r: ℝ) : sqrt (-r) = sqrt r := by
  unfold sqrt sqrt_set
  congr ; ext x
  rw [neg_norm]

@[simp]
def sqrt_zero : sqrt 0 = 0 := by
  apply flip le_antisymm
  apply nonneg_sqrt
  apply csSup_le; apply sqrt_set_nonempty
  intro x hx
  rw [mem_sqrt_set, norm_zero] at hx
  rcases lt_trichotomy x 0 with h | h | h
  · rw [←neg_lt_neg_iff] at h
    have := mul_lt_mul_of_pos_left _ _ h _ h
    rw [neg_zero, mul_zero, ←neg_mul_left,
      ←neg_mul_right, neg_neg, ←npow_two] at this
    nomatch not_le_of_lt this hx
  · rw [h]
  · have := mul_lt_mul_of_pos_left _ _ h _ h
    rw [mul_zero, ←npow_two] at this
    nomatch not_le_of_lt this hx

def of_sq_le_sq (a b: ℝ) : 0 ≤ a -> 0 ≤ b -> a ^ 2 ≤ b ^ 2 -> a ≤ b := by
  intro ha hb h
  rw [←not_lt]; intro g
  rcases lt_or_eq_of_le hb with hb | rfl
  · have := mul_lt_mul_of_pos_left _ _ g _ hb
    rw [←npow_two] at this
    replace := lt_of_le_of_lt h this
    rw [npow_two] at this
    apply not_le_of_lt this
    apply mul_le_mul_of_nonneg_right
    apply le_of_lt; assumption
    assumption
  · rw [zero_npow, npow_two] at h
    apply not_le_of_lt (pos_mul_of_pos _ _ g g)
    assumption
    decide

def sq_inj (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b) : a ^ 2 = b ^ 2 -> a = b := by
  intro h
  apply le_antisymm
  apply of_sq_le_sq; assumption; assumption; rw [h]
  apply of_sq_le_sq; assumption; assumption; rw [h]

def sqrt_mul (a b: ℝ) : (a * b).sqrt = a.sqrt * b.sqrt := by
  apply sq_inj
  apply nonneg_sqrt
  apply nonneg_mul
  apply nonneg_sqrt
  apply nonneg_sqrt
  rw [mul_npow, sq_sqrt, sq_sqrt, sq_sqrt, norm_mul]

@[simp]
def of_sqrt_eq_zero (x: ℝ) : sqrt x = 0 -> x = 0 := by
  intro h
  have : x.sqrt ^ 2  = 0 := by rw [h, zero_npow_succ]
  rw [Real.sq_sqrt] at this
  apply of_norm_eq_zero
  assumption

@[simp]
def sqrt_ne_zero (x: ℝ) (hx: x ≠ 0) : sqrt x ≠ 0 := by
  intro h; apply hx; apply of_sqrt_eq_zero
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply sqrt_ne_zero <;> invert_tactic)

end Real

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

def gm_le_am (a b: ℝ) (ha: 0 ≤ a) (hb: 0 ≤ b) : (a * b).sqrt ≤ (a + b) /? (2: ℕ) := by
  have := nonneg_sq (a.sqrt - b.sqrt)
  rw [sub_sq, sub_eq_add_neg, add_comm_right, sq_sqrt, sq_sqrt,
    le_add_iff_sub_le, zero_sub, neg_neg, ←sqrt_mul] at this
  have := mul_le_mul_of_nonneg_left this ((2: ℕ)⁻¹?) ?_
  rwa [←mul_assoc, inv?_mul_cancel, one_mul, mul_comm _ (_ + _), ←div?_eq_mul_inv?,
    abs_eq_of_nonneg, abs_eq_of_nonneg] at this
  assumption
  assumption
  apply le_of_lt; apply pos_inv?; apply pos_natCast

def is_cauchy_eqv.of_sq (a b: ℕ -> ℚ) (ha: ∀i, 0 ≤ a i) (hb: ∀i, 0 ≤ b i) (h: is_cauchy_eqv (fun i => a i * a i) (fun i => b i * b i)) : is_cauchy_eqv a b := by
  intro ε εpos
  have ⟨k, hk⟩ := h (ε * ε) (pos_mul_of_pos _ _ εpos εpos)
  exists k; intro i j hi hj
  rcases lt_or_le (a i + b j) ε with h | h
  · apply lt_of_le_of_lt _ h
    rw [sub_eq_add_neg]
    apply le_trans
    apply norm_add_le_add_norm
    rw [neg_norm, abs_eq_of_nonneg, abs_eq_of_nonneg]
    apply hb
    apply ha
  · have : ‖a i * a i - b j * b j‖ < ε * ε := hk i j hi hj
    rw [show (a i * a i - b j * b j) = (a i + b j) * (a i - b j) from ?_] at this
    replace := mul_lt_mul₀_of_le_of_lt ?_ ?_ (inv?_le_inv? εpos h) this
    rw [←mul_assoc, inv?_mul_cancel, one_mul] at this
    apply lt_of_le_of_lt _ this
    rw [norm_mul, abs_eq_of_nonneg (a i + b j), ←mul_assoc,
      inv?_mul_cancel, one_mul]
    apply nonneg_add; apply ha; apply hb
    apply norm_nonneg
    apply pos_inv?; assumption
    rw [mul_sub, add_mul, add_mul,
      add_comm _ (b j * b j), sub_add,
        add_sub_assoc, mul_comm (a i) (b j), sub_self, add_zero]

def eqv_sqrt_sq (a: CauchySeq ℚ ℚ) (ha: ∀i, 0 ≤ a i) : is_cauchy_eqv (fun i => (sqrt_func a i ^ 2)) a := by
  simp [sqrt_func]
  have := is_cauchy_eqv.add
    (a := fun i => (a i).sqrt_approx i ^ 2 - a i)
    (b := a) (c := fun _ => 0) (d := a)
    ?_ a.is_cauchy
  simp [zero_add, sub_add_assoc, neg_add_cancel, add_zero] at this
  assumption
  have : (CauchySeq.IsNonneg a) := by
    exists a; apply And.intro a.is_cauchy
    exists 0; intro _ _; apply ha
  -- have := CauchySeq.norm_pos_of_ne_zero
  rcases em (CauchySeq.IsPos a)
  intro ε εpos
  simp [sub_zero]; conv => { rhs; intro i j }
  have : CauchySeq.Eventually fun i => 0 < i := by
    exists 1; intro i hi
    apply lt_of_lt_of_le _ hi
    decide
  have ⟨k, hk⟩ := (a.is_cauchy ε εpos).merge this
  let lb := a k - ε
  let ub := a k + ε
  exists k; intro i j hi hj
  clear hj j
  cases i with
  | zero =>
    rw [Nat.le_zero] at hi
    subst k
    have := hk 0 0 (le_refl _) (le_refl _);
    have := this.right; contradiction
  | succ i =>
    replace ⟨hk, x⟩ := hk _ _ hi hi
    rw [Rational.sqrt_approx_err_spec _ _ (ha _)]
    rw [abs_eq_of_nonneg _ (Rational.nonneg_sqrt_approx_err _ _ _)]
    clear x hk this
    rcases lt_or_eq_of_le (ha (i + 1)) with h | h
    · apply lt_of_le_of_lt
      apply Rational.sqrt_approx_err_le lb ub
      sorry
      sorry
      sorry
      sorry
    · simp [←h]
      sorry
  · sorry

unsafe def is_cauchy_eqv.sqrt (a b: CauchySeq ℚ ℚ) (h: a ≈ b) : is_cauchy_eqv (sqrt_func ‖a‖) (sqrt_func ‖b‖) := lcProof

  -- apply is_cauchy_eqv.of_sq
  -- · intro i
  --   apply Rational.sqrt_approx_nonneg
  -- · intro i
  --   apply Rational.sqrt_approx_nonneg
  -- · show is_cauchy_eqv (fun i => ‖a i‖.sqrt_approx i * ‖a i‖.sqrt_approx i) (fun i => ‖b i‖.sqrt_approx i * ‖b i‖.sqrt_approx i)
  --   have := (is_cauchy_eqv.norm h)
  --   have := CauchySeq.trans (c := ‖b‖) ?_ (eqv_sqrt_sq ‖a‖ ?_) (by
  --     apply is_cauchy_eqv.norm (a := a)
  --     assumption)
  --   have := CauchySeq.trans ?_ this (CauchySeq.symm (eqv_sqrt_sq ‖b‖ ?_))
  --   simp [npow_two, sqrt_func] at this
  --   assumption
  --   exact ‖b‖.is_cauchy
  --   intro i; apply norm_nonneg (b i)
  --   exact ‖a‖.is_cauchy
  --   intro i; apply norm_nonneg (a i)

unsafe def computable_sqrt' [LEM] : ℝ -> ℝ :=
  lift (fun s => ofCauchySeq (CauchySeq.ofSeq {
    toFun := sqrt_func ‖s‖
    is_cauchy' := by
      apply is_cauchy_eqv.sqrt
      rfl
  })) <| by
  intro a b h
  apply sound
  apply is_cauchy_eqv.sqrt
  assumption

attribute [implemented_by computable_sqrt'] sqrt

def square_monotone : ∀{a b: ℝ}, 0 ≤ a -> a ≤ b -> a ^ 2 ≤ b ^ 2 := by
  intro a b ha h
  have := mul_le_mul_of_nonneg_left h a ha
  have := le_trans this (mul_le_mul_of_nonneg_right h b (le_trans ha h))
  rwa [npow_two, npow_two]
def square_strict_monotone : ∀{a b: ℝ}, 0 ≤ a -> a < b -> a ^ 2 < b ^ 2 := by
  intro a b ha h
  have := mul_le_mul_of_nonneg_left (le_of_lt h) _ ha
  replace hb : 0 < b := lt_of_le_of_lt ha h
  have := lt_of_le_of_lt this (mul_lt_mul_of_pos_right _ _ h _ hb)
  rwa [npow_two, npow_two]
def of_square_monotone : ∀{a b: ℝ}, 0 ≤ b -> a ^ 2 ≤ b ^ 2 -> a ≤ b := by
  intro a b hb h
  rw [←not_lt]; rw [←not_lt] at h
  intro g; apply h
  apply square_strict_monotone
  assumption
  assumption
def of_square_strict_monotone : ∀{a b: ℝ}, 0 ≤ b -> a ^ 2 < b ^ 2 -> a < b := by
  intro a b ha h
  rw [←not_le] at *; intro g; apply h
  apply square_monotone
  assumption
  assumption

  -- have := mul_le_mul_of_nonneg_left (le_of_lt h) _ ha
  -- replace hb : 0 < b := lt_of_le_of_lt ha h
  -- have := lt_of_le_of_lt this (mul_lt_mul_of_pos_right _ _ h _ hb)
  -- rwa [npow_two, npow_two]

end Real
