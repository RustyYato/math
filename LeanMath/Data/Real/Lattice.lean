import LeanMath.Data.Real.CeilFloor
import LeanMath.Data.Fintype.Algebra.Monoid

namespace Nat

def eq_of_bitwise (a b: ℕ) (h: ∀i: ℕ, (a / 2 ^ i) % 2 = (b / 2 ^ i) % 2) : a = b := by
  sorry

end Nat

namespace Int

def eq_of_bitwise (a b: ℤ) (h: ∀i: ℕ, (a / 2 ^ i) % 2 = (b / 2 ^ i) % 2) : a = b := by
  rcases a.eq_nat_or_neg with ⟨a, rfl | rfl⟩
  <;> rcases b.eq_nat_or_neg with ⟨b, rfl | rfl⟩
  · congr
    replace h := h
    apply Nat.eq_of_bitwise
    intro i
    have : (a: ℤ) / (2 ^ i: ℕ) % (2: ℕ) = (b: ℤ) / (2 ^ i: ℕ) % (2: ℕ) := h i
    rw [←Int.natCast_ediv, ←Int.natCast_ediv,
      ←Int.natCast_emod, ←Int.natCast_emod] at this
    exact Int.ofNat.inj this
  · exfalso; sorry
  · exfalso; sorry
  · congr
    replace h := h
    apply Nat.eq_of_bitwise
    intro i
    have : (-a: ℤ) / (2 ^ i: ℕ) % (2: ℕ) = (-b: ℤ) / (2 ^ i: ℕ) % (2: ℕ) := h i
    rw [Int.neg_ediv, Int.neg_ediv,
      ←Int.natCast_ediv, ←Int.natCast_ediv] at this
    split at this <;> rename_i ha <;> split at this <;> rename_i hb
    rw [sub_zero, sub_zero, Int.neg_emod, Int.neg_emod] at this
    split at this <;> rename_i ha₁
    rw [Int.natCast_dvd_natCast', Nat.dvd_iff_mod_eq_zero] at ha₁
    rw [ha₁]; symm; rw [←Nat.dvd_iff_mod_eq_zero, ←Int.natCast_dvd_natCast']
    split at this
    assumption
    repeat sorry




    -- rw [←Int.natCast_emod, ←Int.natCast_emod] at this
    -- exact Int.ofNat.inj this
  -- induction ha:a.natAbs using Nat.strongRecOn generalizing a b with
  -- | _ norm_a ih =>
  -- by_cases a_ne_zero:a = 0
  -- · subst a_ne_zero
  --   have : 0 = norm_a := ha
  --   subst norm_a; symm
  --   clear this ih
  --   induction hb:b.natAbs using Nat.strongRecOn generalizing b with
  --   | _ norm_b ih =>
  --   apply LEM.byContradiction
  --   intro b_ne_zero
  --   have : (b / 2).natAbs < b.natAbs := by
  --     cases b with
  --     | ofNat b => sorry
  --     | negSucc b =>
  --       clear b_ne_zero
  --       dsimp
  --       rw [Int.negSucc_eq, Int.neg_ediv]
  --       split <;> rename_i h₁
  --       rw [sub_zero, Int.natAbs_neg, ←natCast_succ,
  --         show (2: ℤ) = (2: ℕ) from rfl,
  --         ←Int.natCast_ediv, Int.natAbs_natCast]
  --       refine Nat.bitwise_rec_lemma ?_
  --       nofun
  --       sorry




  --   sorry
  -- · sorry

end Int

namespace Real

attribute [local irreducible] Rational.lift Rational.lift₂ Rational.lift_with

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

end Real

namespace Real

variable [LEM]

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

def of_monotone_bounded_above [LEM] (f: ℕ -> ℚ) (mono: Monotone f) (bounded: (Set.range f).BoundedAbove) : CauchySeq ℚ ℚ where
  toFun := f
  is_cauchy' := by
    rw [show f = fun i => - - f i from ?_]
    apply is_cauchy_eqv.neg
    apply (of_antitone_bounded_below (fun i => -f i) _ _).is_cauchy
    · intro i j h
      dsimp; rw [neg_le_neg_iff]
      apply mono
      assumption
    · obtain ⟨B, hB⟩ := bounded
      exists -B
      rintro _ ⟨i, rfl⟩
      dsimp; rw [neg_le_neg_iff]
      apply hB
      apply Set.mem_range'
    · ext; rw [neg_neg]

private def bit_sum_seq (f: ℕ -> Bool) (offset: ℕ) (i: ℕ) : ℚ :=
  ∑x: Fin i, bif f (x + offset) then (2: ℕ) ^? (-(x.val + offset)) else 0

def bit_sum_seq_succ (f: ℕ -> Bool) (offset: ℕ) (i: ℕ) : bit_sum_seq f offset (i + 1) = (bif f offset then (2: ℕ) ^? (-offset) else 0: ℚ) + bit_sum_seq f (offset + 1) i := by
  unfold bit_sum_seq
  rw [fin_sum_succ]
  simp; congr
  dsimp; congr; ext x
  congr 1
  rw [add_assoc, add_comm 1]
  congr 1
  rw [add_assoc, add_comm 1]

def bit_sum_seq_succ' (f: ℕ -> Bool) (offset: ℕ) (i: ℕ) : bit_sum_seq f offset (i + 1) = (bif f (i + offset) then (2: ℕ) ^? (-(i + offset)) else 0: ℚ) + bit_sum_seq f offset i := by
  unfold bit_sum_seq
  rw [fin_sum_succ_last, add_comm]
  simp

private def two_zpow_pos (n: ℤ) : (0: ℚ) < ((2: ℕ) ^? n: ℚ) := by
  cases n
  · rw [zpow?_ofNat]
    rw [←natCast_npow, ←natCast_zero]
    apply (natCast_lt_natCast _ _).mpr
    apply Nat.two_pow_pos
  · rw [zpow?_negSucc]
    · rw [inv?_npow]
      apply pos_inv?
      rw [←natCast_npow, ←natCast_zero]
      apply (natCast_lt_natCast _ _).mpr
      apply Nat.two_pow_pos
    · decide

private def two_zpow_strict_mono : StrictMonotone (fun n => ((2: ℕ) ^? n: ℚ)) := by
  intro i j h; dsimp
  conv => {
    rhs; arg 2; rw [←add_zero j, ←neg_add_cancel i,
      ←add_assoc, ←sub_eq_add_neg]
  }
  rw [←one_mul ((2: ℕ) ^? i: ℚ), zpow?_add]
  apply mul_lt_mul_of_pos_right
  · revert i j
    suffices ∀i: ℤ, 0 < i -> 1 < ((2: ℕ) ^? i: ℚ) by
      intro i j h; apply this
      rwa [lt_sub_iff_add_lt, zero_add]
    intro i hi
    match i with
    | (n + 1: ℕ) =>
    clear hi
    rw [zpow?_ofNat, ←natCast_npow, ←natCast_one,
      natCast_lt_natCast]
    exact Nat.one_lt_two_pow' n
  · apply two_zpow_pos
  · decide

private def bit_sum_seq_nonneg (f: ℕ -> Bool) (o: ℕ) (i: ℕ) : 0 ≤ bit_sum_seq f o i := by
  induction i generalizing o with
  | zero => rfl
  | succ n ih =>
    rw [bit_sum_seq_succ]
    cases f o <;> dsimp
    rw [zero_add]; apply ih
    apply flip nonneg_add
    apply ih
    apply le_of_lt
    apply two_zpow_pos

private def bit_sum_seq_monotone (f: ℕ -> Bool) (o: ℕ) : Monotone (bit_sum_seq f o) := by
  intro a b h
  unfold bit_sum_seq
  rw [fin_sum_min _ _ h]
  dsimp; apply le_add_right
  conv => {
    rhs; rhs; intro i
    conv => { arg 1; rw [add_comm_right, add_assoc] }
    conv => { lhs; arg 2; rw [add_comm_right, add_assoc] }
  }
  apply bit_sum_seq_nonneg f (o + a)

private def bit_sum_seq_lt (f: ℕ -> Bool) : bit_sum_seq f o i < ((2: ℕ) ^? (-o + 1): ℚ) := by
  induction i generalizing o with
  | zero => apply two_zpow_pos
  | succ n ih =>
    rw [bit_sum_seq_succ]
    cases f o <;> dsimp
    rw [zero_add]
    apply lt_trans
    · apply ih
    · apply two_zpow_strict_mono
      apply add_lt_add_right
      rw [neg_lt_neg_iff]
      apply Int.lt_succ
    rw [zpow?_succ, mul_comm, two_mul]
    apply add_lt_add_left
    have := @ih (o + 1)
    conv at this => {
      rhs; arg 2; rw [natCast_succ, neg_add_rev, add_comm (-1),
        add_assoc, neg_add_cancel, add_zero]
    }
    assumption
    decide

def bit_sum_offset (f: ℕ -> Bool) (o: ℕ) : ℝ :=
  Real.ringEquivCauchySeq.symm <| CauchySeq.ofSeq (
    of_monotone_bounded_above (bit_sum_seq f o) (bit_sum_seq_monotone f _) <| by
      exists (2: ℕ); rintro _ ⟨i, rfl⟩
      rw [←one_mul ((2: ℕ): ℚ)]
      apply le_of_lt
      apply lt_of_lt_of_le
      apply bit_sum_seq_lt
      rw [zpow?_succ, ←inv?_zpow?]
      apply mul_le_mul_of_nonneg_right _ _ (by decide)
      decide
      · rw [zpow?_ofNat, ←one_inv?, inv?_npow]
        apply inv?_le_inv?
        decide
        rw [←natCast_npow, ←natCast_one, natCast_le_natCast]
        exact Nat.one_le_two_pow
      decide
  )

def bit_sum (f: ℕ -> Bool) : ℝ := bit_sum_offset f 1

noncomputable def testBit (r: ℝ) (i: ℤ) : Bool :=
  (r /? ((2: ℕ) ^? i: ℚ)).floor % 2 = 1

def _root_.Rational.floor (x: ℚ) : ℤ :=
  x.num / x.den

def ratTestBit (r: ℚ) (i: ℤ) : Bool :=
  (r /? ((2: ℕ) ^? i: ℚ)).floor % 2 == 1

def ext_test_bit (a b: ℝ) : (∀i, a.testBit i = b.testBit i) -> a = b := by
  intro h; apply eq_of_lim_eq_zero
  intro ε εpos
  let s (i: ℤ) (r: ℝ) := (r /? ((2: ℕ) ^? i: ℚ)).floor
  have (i: ℤ) : s i a = s i b := by
    unfold s
    unfold testBit at h
    sorry
  -- have ⟨na, hna⟩ := archimedean_iff_nat_lt.mp inferInstance a
  -- have ⟨nb, hnb⟩ := archimedean_iff_nat_lt.mp inferInstance b
  -- have ⟨nε, hnε⟩ := archimedean_iff_nat_lt.mp inferInstance (ε⁻¹?)
  -- have : ∃n: ℕ, ((2: ℕ) ^? (-n): ℚ) < ε ∧ s n a = s n b := by
  --   have : 0 < nε := by
  --     rw [←natCast_lt_natCast (α := ℚ), natCast_zero]
  --     apply lt_trans (pos_inv? _ εpos)
  --     assumption
  --   refine ⟨na ⊔ nb ⊔ nε, ?_, ?_⟩
  --   · rw [←inv?_zpow? _ _ (by decide), zpow?_ofNat]
  --     apply flip <| lt_of_le_of_lt (b := (nε: ℚ)⁻¹?)
  --     have := inv?_lt_inv? (pos_inv? _ εpos) hnε
  --     rwa [inv?_inv?] at this
  --     rw [inv?_npow]; apply inv?_le_inv?
  --     rwa [←natCast_zero, natCast_lt_natCast]
  --     rw [←natCast_npow, natCast_le_natCast]
  --     apply le_trans
  --     show nε ≤ 2 ^ nε
  --     exact nat_le_two_pow nε
  --     refine Nat.pow_le_pow_right ?_ ?_
  --     decide
  --     apply right_le_max
  --   · unfold s
  --     have := h (na ⊔ nb ⊔ nε)
  --     replace :
  --       (a /? ↑((2: ℕ) ^? (na ⊔ nb ⊔ nε: ℕ): ℚ)).floor % 2 =
  --       (b /? ↑((2: ℕ) ^? (na ⊔ nb ⊔ nε: ℕ): ℚ)).floor % 2 := by
  --       sorry
  --     unfold testBit at this


  --     -- simp only [Int.max_assoc, decide_eq_decide] at this

  --     sorry
  -- clear na nb nε hna hnb hnε

  -- let I : Set ℝ := Set.Ico (S )
  sorry

def bit_sum_true_eq_one : (bit_sum fun  _=> true) = 1 := by
  apply sound
  intro ε εpos
  show CauchySeq.Eventually₂ fun i j => ‖(bit_sum_seq (fun _ => true) 1 i - 1: ℚ)‖ < ε
  let S : Set ℕ := { Mem n := (2 ^ n)⁻¹? < ε }
  have ⟨k, hk⟩ : S.Nonempty := by
    have ⟨n, hn⟩ := archimedean_iff_nat_lt.mp inferInstance ε⁻¹?
    exists n
    show _ < ε
    have := inv?_lt_inv? ?_ hn
    rw [inv?_inv?] at this
    apply lt_of_le_of_lt _ this
    apply pos_inv?; assumption
    apply inv?_le_inv?
    apply lt_trans _ hn
    apply pos_inv?; assumption
    show n ≤ ((2: ℕ) ^ n: ℚ)
    rw [←natCast_npow, natCast_le_natCast]
    exact nat_le_two_pow n
  exists k; intro i j hi hj
  apply lt_of_le_of_lt _ hk
  rw [norm_sub, abs_eq_of_nonneg _ (by
    rw [le_sub_iff_add_le, zero_add]
    apply le_of_lt
    apply bit_sum_seq_lt)]
  clear hj j
  clear hk S ε εpos
  rw [←inv?_npow _ _ (by decide), ←zpow?_ofNat, inv?_zpow?]
  show _ ≤ ((2: ℕ) ^? _: ℚ)
  induction i generalizing k with
  | zero =>
    cases Nat.le_zero.mp hi
    rfl
  | succ i ih =>
    rw [bit_sum_seq_succ']
    dsimp
    rw [sub_add, sub_eq_add_neg, add_le_iff_le_sub]
    rw [sub_eq_add_neg _ (-_), neg_neg]
    replace hi := Or.symm (lt_or_eq_of_le hi)
    rcases hi with hi | hi
    · subst k
      conv in (Nat.cast i + 1: ℤ) =>  { rw [←natCast_succ] }
      rw [←two_mul, mul_comm, ←zpow?_succ _ _ (by decide)]
      conv in (-Nat.cast (i + 1) + 1) => {
        rw [natCast_succ, neg_add_rev, add_comm (-1), add_assoc,
          neg_add_cancel, add_zero]
      }
      apply ih; rfl
    · rw [Nat.lt_succ_iff] at hi
      apply le_trans
      apply ih _ hi
      apply le_add_right
      apply le_of_lt
      apply two_zpow_pos

private noncomputable def bit_sum_func (r: ℝ) (acc: ℚ) (i: ℕ) : ℕ -> Bool
| 0 => acc < r
| n + 1 =>
  let q := acc + 2 ^ i
  if r < q then
    bit_sum_func r acc (i + 1) n
  else
    bit_sum_func r q (i + 1) n

def bit_sum_spec (r: ℝ) : r ∈ Set.Icc 0 1 ↔ r ∈ Set.range bit_sum := by
  symm; apply Iff.intro
  · rintro ⟨f, rfl⟩
    apply And.intro
    · apply le_cauchy_of_pointwise
      exists 0; intro i hi
      rw [←ratCast_zero, ratCast_le_ratCast]
      apply bit_sum_seq_nonneg
    · apply cauchy_le_of_pointwise
      exists 0; intro i hi
      rw [←ratCast_one, ratCast_le_ratCast]
      show bit_sum_seq f 1 i ≤ 1
      apply le_of_lt
      apply bit_sum_seq_lt
  · intro r_mem
    by_cases hr:r = 1
    · subst r; clear r_mem
      exists fun _ => true
      rw [bit_sum_true_eq_one]
    · replace r_mem : r ∈ Set.Ico 0 1 := by
        apply And.intro r_mem.left
        apply lt_of_le_of_ne
        exact r_mem.right; assumption
      clear hr
      exists fun i => testBit r i
      sorry
      -- rcases (lt_trichotomy (bit_sum (fun i => r.testBit i)) r) with h | h | h
      -- · exfalso
      --   have ⟨q, lt_rat, _⟩ := exists_rat_between.mp h
      --   sorry
      -- · assumption
      -- · exfalso
      --   sorry

-- noncomputable def exists_monotone_decreasing_eqv (r: ℝ) : ℕ -> ℚ
-- | 0 => sorry
-- | i => sorry

-- def exists_monotone_decreasing_eqv (r: ℝ) : ∃c: CauchySeq ℚ ℚ, r = Real.ringEquivCauchySeq.symm c.ofSeq ∧ Antitone c ∧ (Set.range c).BoundedBelow := by
--   rcases lt_trichotomy 0 r with nonneg | rfl | nonpos
--   · sorry
--   · exists 0
--     apply And.intro rfl
--     apply And.intro
--     · intro _ _ _; rfl
--     · exists 0; rintro _ ⟨_, rfl⟩
--       rfl
--   · sorry

-- def is_cauchy_eqv.cast (a b: ℕ -> ℚ) (h: is_cauchy_eqv a b) : is_cauchy_eqv (fun i => (a i: ℝ)) (fun i => (b i: ℝ)) := by
--   intro ε εpos
--   have ⟨ε', ε'_pos, ε'_lt_ε⟩ := exists_rat_between.mp εpos
--   replace ε'_pos : 0 < ε' := by rwa [←ratCast_lt_ratCast (α := ℝ), ratCast_zero]
--   have ⟨k, hk⟩ := h ε' ε'_pos
--   exists k; intro i j hi hj
--   dsimp; rw [←apply_ratCastHom (a i), ←apply_ratCastHom (b j), ←map_sub,
--     apply_ratCastHom]
--   apply lt_trans _ ε'_lt_ε
--   show Rational.cast (α := ℝ) ‖a i - b j‖ < ε'
--   apply ratCast_lt_ratCast.mpr
--   apply hk <;> assumption

-- def is_cauchy_eqv.of_cast (a b: ℕ -> ℚ) (h: is_cauchy_eqv (fun i => (a i: ℝ)) (fun i => (b i: ℝ))) : is_cauchy_eqv a b := by
--   intro ε εpos
--   have ⟨k, hk⟩ := h ε (ratCast_lt_ratCast.mpr εpos)
--   exists k; intro i j hi hj
--   replace hk := hk i j hi hj
--   dsimp at hk
--   rw [←apply_ratCastHom (a i), ←apply_ratCastHom (b j), ←map_sub,
--     apply_ratCastHom] at hk
--   exact ratCast_lt_ratCast.mp hk

-- def castCauchySeq (s: CauchySeq ℚ ℚ) : CauchySeq ℝ ℝ where
--   toFun i := s i
--   is_cauchy' := by
--     apply is_cauchy_eqv.cast
--     exact s.is_cauchy

-- private def castCauchy' : CauchySeq.Completion ℚ ℚ -> CauchySeq.Completion ℝ ℝ :=
--   CauchySeq.lift (CauchySeq.ofSeq ∘ castCauchySeq) <| by
--     intro a b h
--     apply CauchySeq.sound
--     apply is_cauchy_eqv.cast
--     assumption

-- def castCauchy : CauchySeq.Completion ℚ ℚ ↪ CauchySeq.Completion ℝ ℝ where
--   toFun := castCauchy'
--   inj := by
--     intro a b h
--     induction a with | _ a =>
--     induction b with | _ b =>
--     replace h := CauchySeq.exact h
--     replace h := is_cauchy_eqv.of_cast a b h
--     exact CauchySeq.sound h

-- def castCauchy_eq (r: CauchySeq.Completion ℚ ℚ) : castCauchy r = CauchySeq.Completion.const (Real.ofCauchySeq r) := by
--   induction r with | _ r =>
--   show CauchySeq.ofSeq (castCauchySeq r) = _
--   apply CauchySeq.sound
--   intro ε εpos
--   dsimp
--   have ⟨ε', ε'_pos, ε'_lt_ε⟩ := exists_rat_between.mp εpos
--   replace ε'_pos : 0 < ε' := by rwa [←ratCast_lt_ratCast (α := ℝ), ratCast_zero]
--   have ⟨k, hk⟩ := r.is_cauchy _ (pos_div?_natCast ε'_pos 1)
--   exists k; intro i j hi hj; dsimp at hk
--   show ‖(r i: ℝ) - _‖ < ε
--   apply lt_trans _ ε'_lt_ε
--   show ‖(Real.ofCauchySeq ((CauchySeq.const (r i) - r).ofSeq))‖ < _
--   apply CauchySeq.Completion.lt_of_pos
--   show CauchySeq.IsPos _; dsimp
--   refine ⟨ε' /? (2: ℕ), ?_, ?_⟩
--   apply pos_div?_natCast; assumption
--   exists k; intro j hj
--   show ε' /? (2: ℕ) < ε' - ‖r i - r j‖
--   rw [lt_sub_iff_add_lt]; rw (occs := [2]) [←half_add_half ε']
--   apply add_lt_add_left
--   apply hk <;> assumption

-- def of_seq_converges_to (f: ℕ -> ℚ) (h: ∃r, is_cauchy_eqv (fun i => (f i: ℝ)) (fun _ => r)) : ℝ :=
--   Real.ofCauchySeq <| CauchySeq.ofSeq <| {
--     toFun := f
--     is_cauchy' := by
--       replace ⟨r, h⟩ := h
--       have := CauchySeq.trans (CauchySeq.const r).is_cauchy h (CauchySeq.symm h)
--       exact is_cauchy_eqv.of_cast _ _ this
--   }

-- def of_seq_converges_to_eq (f: ℕ -> ℚ) (r: ℝ) (h: is_cauchy_eqv (fun i => (f i: ℝ)) (fun _ => r)) : of_seq_converges_to f ⟨r, h⟩ = r := by
--   induction r using cau_ind with | _ r =>
--   apply sound
--   show is_cauchy_eqv f r
--   apply is_cauchy_eqv.of_cast
--   apply CauchySeq.trans (CauchySeq.const _).is_cauchy h
--   dsimp
--   show is_cauchy_eqv _ (castCauchySeq r)
--   apply CauchySeq.exact
--   symm; apply castCauchy_eq r.ofSeq

end Real
