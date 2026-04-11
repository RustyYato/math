import LeanMath.Data.Real.CeilFloor

namespace Real

variable [LEM]

private def CauchySeq.Eventually₂_of_le (P: ℕ -> ℕ -> Prop) :
  Relation.IsSymm P ->
  (CauchySeq.Eventually₂ fun i j => i ≤ j -> P i j) ->
  (CauchySeq.Eventually₂ fun i j => P i j) := by
  intro symm ⟨k, hk⟩
  exists k; intro i j hi hj
  rcases le_total i j with h | h
  apply hk; assumption; assumption; assumption
  apply symm.symm
  apply hk; assumption; assumption; assumption

private def nat_le_two_pow (n: ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [npow_succ, Nat.mul_two]
    apply Nat.add_le_add; assumption
    apply Nat.one_le_two_pow

def exists_rat_between {a b: ℝ} : a < b ↔ ∃q: ℚ, a < q ∧ q < b := by
  apply flip Iff.intro
  · intro ⟨q, ha, hb⟩
    exact lt_trans ha hb
  intro h
  have : 0 < b - a := by rwa [lt_sub_iff_add_lt, zero_add]
  have ⟨d, hn⟩ := archimedean_iff_nat_lt.mp inferInstance (b - a)⁻¹?

  have d_ne_zero : d ≠ 0 := by
    intro rfl
    rw [natCast_zero] at hn
    apply Relation.asymm hn
    apply pos_inv?
    assumption
  have a_add_ninv_lt_b : a + (d: ℝ)⁻¹? < b := by
    rw [add_lt_iff_lt_sub, sub_eq_add_neg, add_comm,
      lt_add_iff_sub_lt, ←neg_lt_neg_iff, neg_neg, neg_sub]
    rw [←inv?_inv? (b - a)]
    apply inv?_lt_inv?
    apply pos_inv?; assumption
    assumption
  let n := (a * d).floor + 1
  let q : Rational := Rational.mk {
    num := n
    den := d
    den_ne_zero := d_ne_zero
  }
  have d_pos : 0 < (d: ℝ) := by
    match d with
    | _ + 1 => apply pos_natCast
    | 0 =>
      rw [natCast_zero] at hn
      exfalso; apply Relation.asymm hn
      apply pos_inv?; assumption
  exists q
  apply And.intro
  · rw [ratCast_mk]; dsimp
    apply lt_of_mul_lt_mul_of_pos_left
    exact d_pos
    rw (occs := [2]) [mul_comm]
    rw [div?_mul_cancel]
    rw [mul_comm]
    unfold n; rw [intCast_add, intCast_one]
    apply lt_floor_succ
    apply le_refl
  · rw [ratCast_mk]; dsimp
    apply lt_of_le_of_lt _ a_add_ninv_lt_b
    unfold n
    rw [intCast_add, intCast_one, add_div?, one_div?]
    apply add_le_add_right
    apply le_of_mul_le_mul_of_pos_left
    exact d_pos; rw [mul_comm, div?_mul_cancel, mul_comm]
    apply floor_le

def le_cauchy_of_pointwise (a: ℝ) (c: CauchySeq ℚ ℚ) : (CauchySeq.Eventually fun i => a ≤ c i) -> a ≤ Real.ringEquivCauchySeq.symm (CauchySeq.ofSeq c) := by
  intro h; rw [←not_lt]; intro g
  replace ⟨q, c_lt_q, q_lt_a⟩ := exists_rat_between.mp g
  rw [←not_le] at c_lt_q; apply c_lt_q; clear c_lt_q
  apply CauchySeq.le_of_eventually_le
  obtain ⟨k, hk⟩ := h; exists k
  intro i hi; dsimp
  have : a ≤ c i := hk i hi
  rw [←ratCast_le_ratCast (α := ℝ)]
  apply le_trans _ this
  apply le_of_lt; assumption

def cauchy_le_of_pointwise (a: ℝ) (c: CauchySeq ℚ ℚ) : (CauchySeq.Eventually fun i => c i ≤ a) -> Real.ringEquivCauchySeq.symm (CauchySeq.ofSeq c) ≤ a := by
  intro h; rw [←not_lt]; intro g
  replace ⟨q, a_lt_q, q_lt_c⟩ := exists_rat_between.mp g
  rw [←not_le] at q_lt_c; apply q_lt_c; clear q_lt_c
  apply CauchySeq.le_of_eventually_le
  obtain ⟨k, hk⟩ := h; exists k
  intro i hi; dsimp
  have : c i ≤ a := hk i hi
  rw [←ratCast_le_ratCast (α := ℝ)]
  apply le_trans this
  apply le_of_lt; assumption

def nonneg_of_forall_gt (r: ℝ) : (∀ε: ℚ, 0 < ε -> -ε ≤ r) -> 0 ≤ r := by
  intro h; rw [←not_lt]; intro g
  have ⟨q, r_lt_q, q_lt_zero⟩ := exists_rat_between.mp g
  have := h (-q) (by
    rw [←neg_zero, neg_lt_neg_iff]
    rwa [←ratCast_zero, ratCast_lt_ratCast] at q_lt_zero)
  rw [←apply_ratCastHom, map_neg, neg_neg, apply_ratCastHom] at this
  exact not_le_of_lt r_lt_q this

def eventually_two_pow_inv_lt_rat (q: ℚ) (hq: 0 < q) : CauchySeq.Eventually fun i: ℕ => ((2: ℕ) ^ i: ℚ)⁻¹? < q := by
  have ⟨n, hn⟩ := archimedean_iff_nat_lt.mp inferInstance q⁻¹?
  replace hn := lt_of_lt_of_le hn ((natCast_le_natCast _ _).mpr (nat_le_two_pow _))
  rw [natCast_npow] at hn
  have := inv?_lt_inv? (pos_inv? _ hq) hn; rw [inv?_inv?] at this
  exists n
  intro i hi
  apply lt_of_le_of_lt _ this
  apply inv?_le_inv?
  rw [←natCast_npow, ←natCast_zero]
  apply (natCast_lt_natCast _ _).mpr
  exact Nat.two_pow_pos n
  rw [←natCast_npow, ←natCast_npow]
  apply (natCast_le_natCast _ _).mpr
  refine Nat.pow_le_pow_right ?_ hi
  decide

def eventually_two_pow_inv_lt_real (r: ℝ) (hr: 0 < r) : CauchySeq.Eventually fun i: ℕ => ((2: ℕ) ^ i: ℚ)⁻¹? < r := by
  have ⟨q, qpos, q_lt_r⟩ := exists_rat_between.mp hr
  rw [←ratCast_zero, ratCast_lt_ratCast] at qpos
  have ⟨n, hn⟩ := eventually_two_pow_inv_lt_rat _ qpos
  exists n; intro i hi
  apply lt_trans _ q_lt_r
  exact ratCast_lt_ratCast.mpr (hn i hi)

instance : CauchySeq.IsVectorSpace ℚ ℚ := inferInstance

def eventually_close (a: CauchySeq ℚ ℚ) : ∀ε: ℚ, 0 < ε -> CauchySeq.Eventually fun i => ‖Real.equivCauchySeq.symm (CauchySeq.ofSeq a) - a i‖ < ε := by
  intro ε εpos
  have ⟨k, hk⟩ := a.is_cauchy _ (pos_div?_natCast εpos 1)
  exists k; intro i hi; dsimp at hk
  let c := a - CauchySeq.const (a i)
  show Real.ringEquivCauchySeq.symm ‖c‖.ofSeq < _
  have (m: ℕ) (hm: k ≤ m) : ‖c m‖ < ε /? (2: ℕ) := hk _ _ hm hi
  apply lt_of_le_of_lt
  show _ ≤ ((ε /? (2: ℕ): ℚ): ℝ)
  apply cauchy_le_of_pointwise
  exists k; intro j hj; dsimp
  apply le_of_lt; rw [ratCast_lt_ratCast]; apply this
  assumption
  rw [ratCast_lt_ratCast, ←add_zero (ε /? (2: ℕ))]; rw (occs := [2]) [←half_add_half ε]
  apply add_lt_add_left
  apply pos_div?_natCast
  assumption

private def lub_of_ub (U: Set ℝ) (h: U.Nonempty) (hU: U.BoundedAbove) : existsUnique fun r => U.IsLUB r := by
  suffices ∃r, U.IsLUB r by
    obtain ⟨r, hr⟩ := this
    refine ⟨_, hr, ?_⟩
    intro s hs
    apply le_antisymm
    apply hr.right
    intro a ha
    apply hs.left
    assumption
    apply hs.right
    intro a ha
    apply hr.left
    assumption
  let S (n: ℕ) := Set.ofMem fun x: ℤ => (((x: ℚ) /? (2 ^ n: ℚ): ℚ): ℝ) ∈ U.upperBounds
  have Snonempty (n: ℕ) : (S n).Nonempty := by
    obtain ⟨r, hr⟩ := hU
    have ⟨k, hk⟩ := archimedean_iff_int_le.mp (inferInstance: IsArchimedean ℝ) (r * (2 ^ n: ℚ))
    exists k
    intro a ha
    have := mul_le_mul_of_nonneg_right hk (2 ^ n: ℚ)⁻¹? (by
      apply le_of_lt; apply pos_inv?
      rw [←ratCast_zero]; apply ratCast_lt_ratCast.mpr
      show (0: ℚ) < (2: ℕ) ^ n
      rw [←natCast_npow, ←natCast_zero]
      apply (natCast_lt_natCast _ _).mpr
      exact Nat.two_pow_pos n)
    rw [mul_assoc, mul_inv?_cancel, mul_one, ←div?_eq_mul_inv?] at this
    replace this : r ≤ Real.ofRat k /? (Real.ofRat (2 ^ n: ℚ)) := this
    rw [map_div?'] at this
    apply le_trans _ this
    apply hr
    assumption
  have Sbounded (n: ℕ) : (S n).BoundedBelow := by
    obtain ⟨x, hx⟩ := h
    exists (x * (2 ^ n: ℚ)).floor
    intro y hy
    have := hy x hx
    apply (intCast_le_intCast (α := ℝ) _ _).mp
    apply le_trans; apply floor_le
    apply le_trans
    apply mul_le_mul_of_nonneg_right this
    show 0 ≤ Rational.cast ((2: ℕ) ^ _)
    rw [←natCast_npow, ratCast_natCast]
    apply nonneg_natCast
    rw [←ratCast_mul, div?_mul_cancel, ratCast_intCast]

  let a (i: ℕ) := ((⨅ (S i): ℤ): ℚ) /? (2: ℕ) ^ i

  have (x: ℕ) : x ≤ 2 ^ x := by
    induction x with
    | zero => decide
    | succ x ih =>
      rw [npow_succ, Nat.mul_two]
      apply Nat.add_le_add; assumption
      apply Nat.one_le_two_pow
  have in_ub (i: ℕ) : (a i: ℝ) ∈ U.upperBounds := Int.csInf_mem (S _) (Snonempty _) (Sbounded _)
  have not_in_ub (i: ℕ) : ((a i - (1: ℚ) /? ((2: ℕ) ^ i): ℚ): ℝ) ∉ U.upperBounds := by
    intro g
    simp [a, ←sub_div?] at g
    rw [←intCast_one, ←intCast_sub] at g
    apply not_le_of_lt _ (csInf_le (s := S i) (Sbounded i) g)
    rw [sub_eq_add_neg]; rw (occs := [2]) [←add_zero (⨅ (S i))]
    apply add_lt_add_left
    decide

  let s: CauchySeq ℚ ℚ := {
    toFun := a
    is_cauchy' := by
      intro ε εpos
      have : ∃N, (1 /? ((2: ℕ) ^ N: ℚ)) < ε := by
        have ⟨n, hn⟩ := archimedean_iff_nat_lt.mp inferInstance (1 /? ε)
        -- have :=
        replace hn := lt_of_lt_of_le hn ((natCast_le_natCast (α := ℚ) _ _).mpr (this _))
        exists n
        have := mul_lt_mul_of_pos_right _ _ hn (ε /? (2 ^ n)) ?_
        rw [div?_eq_mul_inv?, one_mul, ←mul_div?_assoc, inv?_mul_cancel, ←mul_div?_assoc, mul_comm, mul_div?_assoc,
          natCast_npow] at this
        erw [div?_self, mul_one] at this
        assumption
        rw [div?_eq_mul_inv?]
        apply pos_mul_of_pos
        assumption
        apply pos_inv?
        show (0: ℚ) < (2: ℕ) ^ n
        rw [←natCast_zero, ←natCast_npow]
        apply (natCast_lt_natCast _ _).mpr
        exact Nat.two_pow_pos n
      obtain ⟨N, hN⟩ := this
      apply CauchySeq.Eventually₂_of_le
      · refine ⟨?_⟩; intro i j h
        rwa [norm_sub]
      exists N; intro i j hi hj i_le_j
      show ‖a i - a j‖ < ε
      apply lt_of_le_of_lt _ hN
      have hai : (a i: ℝ) ∈ U.upperBounds := in_ub _
      have haj : (a j: ℝ) ∈ U.upperBounds := in_ub _
      have hai' : ((a i - (1: ℚ) /? ((2: ℕ) ^ i): ℚ): ℝ) ∉ U.upperBounds := not_in_ub _
      have haj' : ((a j - (1: ℚ) /? ((2: ℕ) ^ j): ℚ): ℝ) ∉ U.upperBounds := not_in_ub _
      have lt₀ : a j - ((1: ℚ) /? (2: ℕ) ^ j) < a i := by
        rw [←not_le]
        have := Set.not_mem_ub_lt_mem_ub (U := U) _ _ haj' hai
        rwa [ratCast_le_ratCast] at this
      have lt₁ : a i - ((1: ℚ) /? (2: ℕ) ^ i) < a j := by
        rw [←not_le]
        have := Set.not_mem_ub_lt_mem_ub (U := U) _ _ hai' haj
        rwa [ratCast_le_ratCast] at this
      rw [sub_lt_iff_lt_add, add_comm, ←sub_lt_iff_lt_add] at lt₀
      rw [sub_lt_iff_lt_add, add_comm, ←sub_lt_iff_lt_add] at lt₁
      rw [abs_eq_max, neg_sub]; apply max_le
      apply le_trans; apply le_of_lt; exact lt₁
      · rw [one_div?, one_div?]
        apply le_of_mul_le_mul_of_pos_left
        show 0 < ((2: ℕ) ^ i * (2: ℕ) ^ N: ℚ)
        rw [←npow_add, ←natCast_npow, ←natCast_zero]
        apply (natCast_lt_natCast _ _).mpr
        apply Nat.two_pow_pos
        rw [mul_comm, ←mul_assoc, inv?_mul_cancel, one_mul,
          mul_assoc, mul_inv?_cancel, mul_one]
        rw [←natCast_npow, ←natCast_npow, natCast_le_natCast]
        refine Nat.pow_le_pow_right ?_ hi
        decide
      apply le_trans; apply le_of_lt; exact lt₀
      · rw [one_div?, one_div?]
        apply le_of_mul_le_mul_of_pos_left
        show 0 < ((2: ℕ) ^ j * (2: ℕ) ^ N: ℚ)
        rw [←npow_add, ←natCast_npow, ←natCast_zero]
        apply (natCast_lt_natCast _ _).mpr
        apply Nat.two_pow_pos
        rw [mul_comm, ←mul_assoc, inv?_mul_cancel, one_mul,
          mul_assoc, mul_inv?_cancel, mul_one]
        rw [←natCast_npow, ←natCast_npow, natCast_le_natCast]
        refine Nat.pow_le_pow_right ?_ hj
        decide
  }
  let s' := Real.ringEquivCauchySeq.symm (CauchySeq.ofSeq s)
  exists s'
  apply And.intro
  · intro r hr
    apply le_cauchy_of_pointwise
    exists 0; intro i hi
    show r ≤ (((⨅ (S i): ℤ) /? (2: ℕ) ^ i: ℚ): ℝ)
    apply Int.csInf_mem (S i) (Snonempty _) (Sbounded _)
    assumption
  · intro u hu
    rw [←zero_add s', add_le_iff_le_sub]
    apply nonneg_of_forall_gt
    intro ε εpos
    have even₀ := eventually_two_pow_inv_lt_rat (ε /? (2: ℕ)) (pos_div?_natCast εpos 1)
    have even₁ := eventually_close s _ (pos_div?_natCast εpos 1)
    obtain ⟨i, hi⟩ := even₀.merge even₁
    replace ⟨inv_lt_ε, diff_ge_ε⟩ := hi i (le_refl _)
    clear even₀ even₁ hi
    replace diff_ge_ε : ‖s' - a i‖ < ((ε /? (2: ℕ): ℚ): ℝ) := diff_ge_ε
    replace inv_lt_ε : ((2: ℕ) ^ i: ℚ)⁻¹? < ε /? (2: ℕ) := inv_lt_ε
    replace diff_ge_ε : -ε /? (2: ℕ) ≤ a i - s' := by
      dsimp at diff_ge_ε
      rw [abs_eq_max] at diff_ge_ε
      have := le_trans left_le_max (le_of_lt diff_ge_ε)
      rwa [←neg_le_neg_iff,
        ←apply_ratCastHom, ←map_neg, apply_ratCastHom,
        neg_sub, neg_div?_left] at this
    have lt : (a i - ((1: ℚ) /? (2: ℕ) ^ i): ℚ) < u := by
      rw [←not_le]
      have := Set.not_mem_ub_lt_mem_ub (U := U) _ _ (not_in_ub i) hu
      assumption
    rw [←add_zero u, ←neg_add_cancel (a i: ℝ),
      ←add_assoc, ←sub_eq_add_neg, add_sub_assoc]
    rw [←apply_ratCastHom, map_sub, apply_ratCastHom, apply_ratCastHom,
      sub_lt_iff_lt_add, add_comm, ←sub_lt_iff_lt_add,
      ←neg_lt_neg_iff, neg_sub, one_div?] at lt
    rw [←ratCast_lt_ratCast (α := ℝ), ←neg_lt_neg_iff] at inv_lt_ε
    replace lt := lt_trans inv_lt_ε lt; clear inv_lt_ε
    apply flip le_trans; apply add_le_add
    exact le_of_lt lt
    exact diff_ge_ε
    rw [←apply_ratCastHom, ←apply_ratCastHom, ←apply_ratCastHom,
      ←map_neg, ←map_neg, neg_div?_left,
      map_div?]
    simp only [map_natCast, half_add_half]
    rfl

noncomputable instance : SupSet ℝ where
  sSup U :=
    open UniqueChoice in
    if hU:U.Nonempty ∧ U.BoundedAbove then
      Classical.choose_unique (lub_of_ub U hU.left hU.right)
    else
      0

noncomputable instance : InfSet ℝ where
  sInf U := sSup U.lowerBounds

private protected def le_csSup : ∀{s} {a: ℝ}, s.BoundedAbove → a ∈ s → a ≤ (⨆ s) := by
  open UniqueChoice in
  intro U u hU hu
  simp [SupSet.sSup]
  rw [dif_pos]
  apply (Classical.choose_unique_spec (Real.lub_of_ub _ _ _)).left
  assumption
  exists u
  assumption
  apply And.intro
  exists u
  assumption

private protected def csSup_le : ∀{s} {a: ℝ}, Set.Nonempty s → a ∈ s.upperBounds → (⨆ s) ≤ a := by
  open UniqueChoice in
  intro U u hU hu
  simp [SupSet.sSup]
  rw [dif_pos]
  rw [←not_lt]; intro h
  have lub := Classical.choose_unique_spec (Real.lub_of_ub U hU ⟨_, hu⟩)
  exact not_lt.mpr (lub.right u hu) h
  apply And.intro
  assumption
  exists u

instance : IsConditionallyCompleteLattice ℝ where
  le_csSup := Real.le_csSup
  csSup_le := Real.csSup_le
  le_csInf := by
    intro U u hU hu
    apply Real.le_csSup
    obtain ⟨x, hx⟩ := hU
    exists x; intro y hy
    apply hy
    assumption
    assumption
  csInf_le := by
    intro U u hU hu
    apply Real.csSup_le
    obtain ⟨x, hx⟩ := hU
    exists x; intro y hy
    apply hy
    assumption

private def sets (ε: ℚ) (f: ℕ -> ℚ) (i: ℕ) : Set ℕ := { Mem j := i < j ∧ ε ≤ f i - f j }
@[implicit_reducible]
private def sets_nonempty (ε: ℚ) (εpos: 0 < ε) (f: ℕ -> ℚ) (i: ℕ)
  (anti: Antitone f)
  (hf: ∀N, ∃i j: ℕ, N ≤ i ∧ N ≤ j ∧ i ≤ j ∧ ε ≤ ‖f i - f j‖)
  : (sets ε f i).Nonempty := by
  have ⟨x, y, hx, hy, x_le_y, diff⟩ := hf i
  rw [abs_eq_of_nonneg] at diff
  have : ε ≤ f i - f y := by
    apply le_trans diff
    rw [sub_eq_add_neg, sub_eq_add_neg]
    apply add_le_add_right
    apply anti
    assumption
  have : i < y := by
    apply lt_of_le_of_ne
    assumption
    intro rfl
    rw [sub_self] at this
    exact not_le_of_lt εpos this
  exists y
  rw [le_sub_iff_add_le, zero_add]
  apply anti; assumption

private noncomputable def reindex (ε: ℚ) (f: ℕ -> ℚ) : ℕ -> ℕ
| 0 => 0
| i + 1 => ⨅ (sets ε f (reindex ε f i))

def of_antitone_bounded_below [LEM] (f: ℕ -> ℚ) (anti: Antitone f) (bounded: (Set.range f).BoundedBelow) : CauchySeq ℚ ℚ where
  toFun := f
  is_cauchy' := by
    intro ε εpos
    apply CauchySeq.Eventually₂_of_le
    refine ⟨?_⟩; intro i j h; rwa [norm_sub]
    apply LEM.byContradiction
    intro h
    simp only [CauchySeq.Eventually₂, not_exists, LEM.not_forall, not_lt] at h
    let sets (i: ℕ) : Set ℕ := Real.sets ε f i
    have sets_nonempty (i: ℕ) : (sets i).Nonempty := by
      apply Real.sets_nonempty
      assumption
      assumption
      intro N; have ⟨x₀, x₁, x₂, x₃, x₄, x₅⟩ := h N
      exact ⟨x₀, x₁, x₂, x₃, x₄, x₅⟩
    let r := reindex ε f
    have rsucc (n: ℕ) : r (n + 1) = (⨅ sets (r n)) := rfl
    have hr (i: ℕ) : i * ε ≤ f (r 0) - f (r i) := by
      rw [←nsmul_eq_natCast_mul]
      induction i with
      | zero => rw [sub_self, zero_nsmul]
      | succ i ih =>
        rw [succ_nsmul, ←add_zero (f (r 0)), ←neg_add_cancel (f (r i)),
          ←add_assoc, ←sub_eq_add_neg, add_sub_assoc]
        apply add_le_add; apply ih
        clear ih
        have := Nat.csInf_mem (sets_nonempty (r i))
        exact this.right
    have ⟨B, hB⟩ := bounded
    replace hB : B ∈ (Set.range (f ∘ r)).lowerBounds := by
      rintro _ ⟨i, rfl⟩
      apply hB; apply Set.mem_range'
    have ⟨N, hN⟩ := archimedean_iff_nat_lt.mp inferInstance ((f (r 0) - B) /? ε)
    have := mul_lt_mul_of_pos_right _ _ hN _  εpos
    rw [div?_mul_cancel] at this
    replace := lt_of_lt_of_le this (hr N)
    rw [sub_eq_add_neg, sub_eq_add_neg, ←not_le, add_le_add_left_iff, not_le, neg_lt_neg_iff] at this
    exact not_le_of_lt this (hB (f (r N)) Set.mem_range')

end Real
