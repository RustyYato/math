import LeanMath.Data.Nat.Prime.Defs
import LeanMath.Data.DirectSum.Defs
import LeanMath.Logic.Relation.Defs

namespace Nat

structure PrimeFactors where
  ofDirectSum :: toDirectSum : DirectSum (fun _: { p: ℕ // IsPrime p } => ℕ)

unsafe instance : Repr PrimeFactors where
  reprPrec a := reprPrec a.toDirectSum

instance : AddMonoidOps ℕ := inferInstance

namespace PrimeFactors

def of_prime (p: ℕ) (h: IsPrime p) : PrimeFactors where
  toDirectSum := DirectSum.ι ⟨p, h⟩ 1

instance : One PrimeFactors where
  one := ⟨0⟩
instance : Mul PrimeFactors where
  mul a b := { toDirectSum := a.toDirectSum + b.toDirectSum }
instance : Pow PrimeFactors ℕ where
  pow a n := { toDirectSum := n • a.toDirectSum }

private def equivMulDirectSum : PrimeFactors ≃* MulOfAdd (DirectSum fun _: { p: ℕ // IsPrime p } => ℕ) where
  toFun := PrimeFactors.toDirectSum
  invFun := PrimeFactors.ofDirectSum
  leftInv _ := rfl
  rightInv _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

instance : IsLawfulPowN PrimeFactors :=
  IsLawfulPowN.lift equivMulDirectSum (fun _ _ => rfl)
instance : IsMonoid PrimeFactors :=
  IsMonoid.lift equivMulDirectSum
instance : IsComm PrimeFactors :=
  IsComm.lift equivMulDirectSum

def list_induction
  {motive: PrimeFactors -> Prop}
  (one: motive 1)
  (cons: ∀p hp ps, motive ps -> motive (of_prime p hp * ps))
  (ps: PrimeFactors) : motive ps := by
  obtain ⟨ps⟩ := ps
  induction ps using DirectSum.list_induction with
  | zero => apply one
  | ι_add p n ih =>
    rw [←mul_one n]
    show motive { toDirectSum := DirectSum.ι _ (n • 1) + _ }
    rw [←DirectSum.smul_ι]
    induction n with
    | zero => rwa [zero_nsmul, zero_add]
    | succ n ih =>
      rw [succ_nsmul, add_comm _ (DirectSum.ι _ _), add_assoc]
      apply cons
      assumption

@[induction_eliminator]
def induction
  {motive: PrimeFactors -> Prop}
  (one: motive 1)
  (prime: ∀p hp, motive (of_prime p hp))
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (ps: PrimeFactors) : motive ps := by
  induction ps using list_induction with
  | one => apply one
  | cons =>
    apply mul
    apply prime
    assumption

private def preEval (f: PrimeFactors) : ℕ :=
  AddOfMul.get (
    DirectSum.lift (M := AddOfMul ℕ) (fun p => {
      toFun n := AddOfMul.mk (p.val ^ n)
      map_zero := rfl
      map_add a b := by rw [npow_add]; rfl
    }) f.toDirectSum
  )

private def eval' : PrimeFactors →* ℕ where
  toFun := preEval
  map_one := by
    show AddOfMul.get (DirectSum.lift _ 0) = _
    rw [map_zero]; rfl
  map_mul a b := by
    show AddOfMul.get (DirectSum.lift _ (_ + _)) = _
    rw [map_add]; rfl

private def eval'_of_prime : eval' (of_prime p hp) = p := by
  show AddOfMul.get (DirectSum.lift _ (DirectSum.ι _ _)) = _
  rw [DirectSum.lift_ι]
  show p ^ 1 = p
  rw [npow_succ, npow_zero, one_mul]

end PrimeFactors

private def existsFactorPow (n: ℕ) (hn: n ≠ 0) : ∃k, n.minFact ^ (n - k) ∣ n := by
  exists (n - 1)
  rw [Nat.sub_sub_eq_min, Nat.min_eq_right, npow_one]
  apply Nat.minFact_dvd
  apply Nat.succ_le_of_lt
  apply Nat.pos_of_ne_zero
  assumption

private def find_lt_existsFactor (n: ℕ) (hn: n ≠ 0) : Nat.find (existsFactorPow n hn) < n := by
  apply Nat.not_le.mp
  intro h; rw [Nat.le_iff_lt_or_eq] at h
  rcases h with h | h
  · have := Nat.find_minimal _ _ h
    rw [Nat.sub_self, npow_zero] at this
    exact this (Nat.one_dvd _)
  · have := Nat.find_minimal (existsFactorPow n hn) (n - 1) ?_
    rw [Nat.sub_sub_self, npow_one] at this
    exact this (Nat.minFact_dvd _)
    apply Nat.succ_le_of_lt
    apply Nat.pos_of_ne_zero
    assumption
    rw [←h]
    match n with
    | n + 1 =>
    apply Nat.lt_succ_self

private def simple_factors_rec_lemma (n: ℕ) (h: 1 < n) : n / (Nat.minFact n) < n := by
  apply Nat.div_lt_of_lt_mul'
  rw (occs := [1]) [←Nat.one_mul n]
  apply (Nat.mul_lt_mul_right' _).mpr
  apply one_lt_prime
  exact Nat.minFact_prime _ (Nat.ne_of_gt h)
  apply Nat.zero_lt_of_lt h

private def simple_factors_ne_zero (n: ℕ) (h: 1 < n) : n / Nat.minFact n ≠ 0 := by
  intro g
  have := Nat.mul_div_cancel_left' (Nat.minFact_dvd n)
  rw [g, mul_zero] at this
  rw [←this] at h
  contradiction

private def simple_factors (n: ℕ) : PrimeFactors :=
  if h:1 < n then
    let m := n.minFact
    PrimeFactors.of_prime m (Nat.minFact_prime _ (Nat.ne_of_gt h)) *
      simple_factors (n / m)
  else
    1
decreasing_by
  apply simple_factors_rec_lemma _ h

def factors_rec_lemma (n: ℕ) (hn: 1 < n) : n / (Nat.minFact n) ^ (n - Nat.find (existsFactorPow n (Nat.ne_zero_of_lt hn))) < n := by
  have npos := Nat.zero_lt_of_lt hn
  have n_ne_zero := Nat.ne_zero_of_lt hn
  apply div_lt_of_lt_mul'
  rw (occs := [1]) [←Nat.one_mul n]
  apply Nat.mul_lt_mul_of_pos_right _ npos
  apply Nat.one_lt_pow
  · intro h
    rw [Nat.sub_eq_zero_iff_le] at h
    exact Nat.not_le_of_lt (find_lt_existsFactor n n_ne_zero) h
  · apply one_lt_prime
    apply Nat.minFact_prime
    intro rfl; contradiction

def factors_rec_ne_zero (n: ℕ) (h: 1 < n) :
  n / Nat.minFact n ^ (n - Nat.find (existsFactorPow n (Nat.ne_zero_of_lt h))) ≠ 0 := by
  let hex := existsFactorPow n (Nat.ne_zero_of_lt h)
  have : Nat.minFact n ^ (n - Nat.find hex) ∣ n := Nat.find_spec hex
  replace := Nat.mul_div_cancel_left' this
  intro h; rw [h, mul_zero] at this
  subst n; contradiction

def factors (n: ℕ) : PrimeFactors :=
  if h₁:1 < n then
    let m := n.minFact
    have existsFactor : ∃k, m ^ (n - k) ∣ n := existsFactorPow _ (Nat.ne_zero_of_lt h₁)
    let k := n - Nat.find existsFactor
    PrimeFactors.of_prime m (n.minFact_prime (Nat.ne_of_gt h₁)) ^ k * (
      (n / (m ^ k)).factors)
  else
    1
decreasing_by
  apply factors_rec_lemma
  match n with
  | n + 2 =>
  apply Nat.succ_lt_succ
  apply Nat.zero_lt_succ

private def factors_eval' (n: ℕ) (hn: n ≠ 0) : PrimeFactors.eval' n.factors = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  unfold factors
  split;
  · dsimp; rw [map_mul,
      map_npow,
      PrimeFactors.eval'_of_prime, ih]
    rw [Nat.mul_div_cancel']

    have (h: ∃ k, n.minFact ^ (n - k) ∣ n) : n.minFact ^ (n - Nat.find h) ∣ n := Nat.find_spec h
    apply this

    · apply factors_rec_lemma
      match n with
      | n + 2 =>
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ
    · apply factors_rec_ne_zero
      assumption
  · rw [map_one]
    match n with
    | 1 => rfl
    | n + 2 =>
      rename_i h
      exfalso; apply h
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ

private def simple_factors_rep (n k: ℕ) (hn: 1 < n) (h: n.minFact ^ k ∣ n) : simple_factors n = PrimeFactors.of_prime n.minFact (Nat.minFact_prime _ (Nat.ne_of_gt hn)) ^ k * simple_factors (n / n.minFact ^ k) := by
  induction k generalizing n with
  | zero => rw [npow_zero, one_mul, npow_zero, Nat.div_one]
  | succ k ih =>
    rcases k with _ | k
    · rw [npow_one] at h
      simp [npow_one]
      rw [simple_factors]
      rw [dif_pos hn]
    rw [simple_factors, dif_pos hn]
    rw [npow_succ, mul_comm _ (PrimeFactors.of_prime _ _), mul_assoc]; dsimp
    congr 1
    have h₁ : n.minFact = (n / n.minFact).minFact := by
      obtain ⟨m, hm⟩ := h
      rw (occs := [2]) [hm]
      rw [Nat.pow_succ, mul_comm _ n.minFact, mul_assoc,
        Nat.mul_div_cancel_left]
      · rw [npow_succ, mul_comm _ n.minFact, mul_assoc]
        rw [Nat.minFact_eq_of_minimal (_ * _) ]
        · apply one_lt_prime
          apply Nat.minFact_prime
          apply Nat.ne_of_gt
          assumption
        · apply Nat.dvd_mul_right
        · intro f fprime hf
          rw [←mul_assoc, mul_comm n.minFact, ←npow_succ] at hf
          replace hf := fprime.irreducible hf
          rcases hf with hf | hf
          · apply Nat.minFact_minimal
            apply one_lt_prime
            assumption
            apply Nat.dvd_trans
            assumption
            rw (occs := [2]) [hm]
            rw [npow_succ _ (k + 1), mul_assoc]
            apply Nat.dvd_mul_right
          · apply Nat.minFact_minimal
            apply one_lt_prime
            assumption
            rw [hm]
            apply Nat.dvd_trans
            assumption
            apply Nat.dvd_mul_left
      · apply Nat.pos_of_ne_zero
        apply IsPrime.ne_zero
        apply Nat.minFact_prime
        apply Nat.ne_of_gt
        assumption
    conv => { rhs; lhs; arg 1; arg 1; rw [h₁] }
    have := ih (n / n.minFact) ?_ ?_
    rw [this]
    simp [←h₁]
    congr 2
    rw [Nat.div_div_eq_div_mul, mul_comm, ←npow_succ]
    · apply (Nat.mul_lt_mul_right' _).mp
      rw [Nat.div_mul_cancel, one_mul]
      apply Nat.lt_of_le_of_ne
      apply Nat.le_of_dvd
      apply Nat.zero_lt_of_lt; assumption
      apply Nat.minFact_dvd
      intro g
      rw (occs := [2]) [←g] at h
      have := Nat.dvd_antisymm h (by
        rw [npow_succ]; apply Nat.dvd_mul_left)
      rw (occs := [2]) [←npow_one n.minFact] at this
      rw [Nat.pow_right_inj'] at this
      nomatch this
      apply one_lt_prime
      apply Nat.minFact_prime
      apply Nat.ne_of_gt
      assumption
      apply Nat.minFact_dvd
      apply Nat.pos_of_ne_zero
      apply IsPrime.ne_zero
      apply Nat.minFact_prime
      apply Nat.ne_of_gt
      assumption
    · rw [←h₁]
      apply (Nat.dvd_div_iff_mul_dvd _).mpr
      rwa [mul_comm, ←npow_succ]
      apply Nat.minFact_dvd

private def factors_eq_simple_factors (n: ℕ) : factors n = simple_factors n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold factors
    dsimp; split
    · rw [simple_factors_rep]; congr
      apply ih
      apply factors_rec_lemma
      assumption
      assumption
      apply Nat.find_spec (existsFactorPow _ _)
      apply Nat.ne_zero_of_lt
      assumption
    · unfold simple_factors
      rwa [dif_neg]

private def simple_factors_one : simple_factors 1 = 1 := by
  unfold simple_factors
  rw [dif_neg]
  apply Nat.lt_irrefl

def factors_one : factors 1 = 1 := by
  unfold factors
  rw [dif_neg]
  apply Nat.lt_irrefl

def factors_prime (p: ℕ) (hp: IsPrime p) : factors p = PrimeFactors.of_prime p hp := by
  have minFact_eq_self : p.minFact = p := by
    rcases prime_def hp p.minFact (Nat.minFact_dvd p) with h | h
    assumption
    have := (minFact_prime p ?_).not_unit (h ▸ inferInstance)
    contradiction
    intro rfl
    exact hp.not_unit inferInstance
  have pow_eq_one : p - Nat.find (existsFactorPow p hp.ne_zero) = 1 := by
    have h := find_spec (existsFactorPow p hp.ne_zero)
    rw (occs := [1]) [minFact_eq_self] at h
    replace h := prime_def hp _ h
    rcases h with h | h
    · replace h := h.trans (npow_one p).symm
      rwa [Nat.pow_right_inj'] at h
      · apply one_lt_prime
        assumption
    · rw [Nat.pow_eq_one] at h
      rcases h with h | h
      subst p; nomatch hp.not_unit inferInstance
      rw [Nat.sub_eq_zero_iff_le] at h
      have := Nat.not_le_of_gt (find_lt_existsFactor p hp.ne_zero) h
      contradiction
  unfold factors
  dsimp; rw [dif_pos (by
    apply one_lt_prime
    assumption)]
  rw [←mul_one (PrimeFactors.of_prime p hp)]; congr
  rw [show find (existsFactorPow p hp.ne_zero) = p - 1 from ?_]
  rw [Nat.sub_sub_self, npow_one]; congr
  · apply Nat.le_of_lt
    apply one_lt_prime
    assumption
  · apply Nat.eq_sub_of_add_eq'
    symm; apply Nat.eq_add_of_sub_eq
    apply Nat.le_of_lt
    apply find_lt_existsFactor
    exact hp.ne_zero
    assumption
  · rw (occs := [1]) [pow_eq_one, minFact_eq_self, npow_one]
    rw [Nat.div_self (Nat.pos_of_ne_zero hp.ne_zero), factors_one]

def factors_mul (a b: ℕ) (ha: a ≠ 0) (hb: b ≠ 0) : factors (a * b) = factors a * factors b := by
  rw [factors_eq_simple_factors, factors_eq_simple_factors, factors_eq_simple_factors]
  induction a using Nat.strongRecOn generalizing b with
  | ind a iha =>
  induction b using Nat.strongRecOn with
  | ind b ihb =>
  have ab_ne_zero : a * b ≠ 0 := by
    intro h; rw [Nat.mul_eq_zero] at h
    rcases h <;> contradiction
  by_cases h₀:a * b ≤ 1
  · have : a * b = 1 := by
      apply Nat.le_antisymm
      assumption
      apply Nat.one_le_of_lt
      apply Nat.pos_of_ne_zero
      assumption
    rw [Nat.mul_eq_one_iff] at this
    obtain ⟨rfl, rfl⟩ := this
    rw [mul_one, simple_factors_one, mul_one]
  · let m := (a * b).minFact
    rw [Nat.not_le] at h₀
    have m_prime: IsPrime m := Nat.minFact_prime _ (Nat.ne_of_gt h₀)
    rw [simple_factors, dif_pos h₀]
    dsimp
    rcases m_prime.irreducible (Nat.minFact_dvd _) with h | h
    · have : a ≠ 1 := by
        intro rfl
        rw [Nat.dvd_one] at h
        subst m
        rw [Nat.one_mul] at h h₀
        have := Nat.minFact_prime b (Nat.ne_of_gt h₀)
        rw [h] at this
        contradiction
      have : a.minFact = m := by
        apply Nat.minFact_eq_of_minimal
        apply one_lt_prime
        assumption
        assumption
        intro k hk ka
        apply Nat.minFact_minimal
        apply one_lt_prime
        assumption
        apply Nat.dvd_trans
        assumption
        apply Nat.dvd_mul_right
      rw (occs := [2]) [simple_factors]
      rw [dif_pos, mul_assoc]
      congr 2; symm; assumption
      unfold m at this h
      rw [this, Nat.mul_comm, Nat.mul_div_assoc, Nat.mul_comm, Nat.mul_comm b]
      apply iha
      apply (Nat.mul_lt_mul_left' _).mp
      rw [Nat.mul_div_cancel_left' h]
      · rw (occs := [1]) [←one_mul a]
        apply (Nat.mul_lt_mul_right' _).mpr
        rw [←this]
        apply one_lt_prime
        apply Nat.minFact_prime
        assumption
        apply Nat.zero_lt_of_ne_zero
        assumption
      · rw [←this]
        apply Nat.zero_lt_of_ne_zero
        intro g
        rw [←this, g, Nat.zero_dvd] at h
        subst a; contradiction
      · intro g
        have := Nat.mul_div_cancel_left' h
        rw [g, mul_zero] at this
        subst a; contradiction
      · intro rfl
        rw [mul_zero] at h₀
        contradiction
      · rw [Nat.mul_comm, ←this]
        apply Nat.minFact_dvd
      · omega
    · have : b ≠ 1 := by
        intro rfl
        rw [Nat.dvd_one] at h
        subst m
        rw [Nat.mul_one] at h h₀
        have := Nat.minFact_prime a (Nat.ne_of_gt h₀)
        rw [h] at this
        contradiction
      have : b.minFact = m := by
        apply Nat.minFact_eq_of_minimal
        apply one_lt_prime
        assumption
        assumption
        intro k hk ka
        apply Nat.minFact_minimal
        apply one_lt_prime
        assumption
        apply Nat.dvd_trans
        assumption
        apply Nat.dvd_mul_left
      rw (occs := [3]) [simple_factors]
      rw [dif_pos, ←mul_assoc, mul_comm _ (PrimeFactors.of_prime _ _), mul_assoc]
      congr 2; symm; assumption
      unfold m at this h
      rw [this, Nat.mul_div_assoc]
      apply ihb
      apply (Nat.mul_lt_mul_left' _).mp
      rw [Nat.mul_div_cancel_left' h]
      · rw (occs := [1]) [←one_mul b]
        apply (Nat.mul_lt_mul_right' _).mpr
        rw [←this]
        apply one_lt_prime
        apply Nat.minFact_prime
        assumption
        apply Nat.zero_lt_of_ne_zero
        assumption
      · rw [←this]
        apply Nat.zero_lt_of_ne_zero
        intro g
        rw [←this, g, Nat.zero_dvd] at h
        subst b; contradiction
      · intro g
        have := Nat.mul_div_cancel_left' h
        rw [g, mul_zero] at this
        subst b; contradiction
      · rw [←this]
        apply Nat.minFact_dvd
      · omega

private def PrimeFactors.eval'_ne_zero (a: PrimeFactors) : PrimeFactors.eval' a ≠ 0 := by
  induction a with
  | one => rw [map_one]; nofun
  | mul a b =>
    intro h; rw [map_mul, mul_eq_zero] at h
    cases h <;> contradiction
  | prime p hp =>
    rw [PrimeFactors.eval'_of_prime]
    exact hp.ne_zero

private def eval'_factors (a: PrimeFactors) : factors (PrimeFactors.eval' a) = a := by
  induction a with
  | one =>
    rw [map_one, factors_one]
  | mul =>
    rw [map_mul, factors_mul]; congr
    apply PrimeFactors.eval'_ne_zero
    apply PrimeFactors.eval'_ne_zero
  | prime p hp => rw [PrimeFactors.eval'_of_prime, factors_prime]

def PrimeFactors.eval : PrimeFactors ↪* ℕ where
  toGroupHom := PrimeFactors.eval'
  inj := by
    intro a b h
    replace h : eval' a = eval' b := h
    have := eval'_factors b
    rwa [←h, eval'_factors] at this

def PrimeFactors.factors_eval (a: PrimeFactors) : factors (eval a) = a := by apply eval'_factors
def PrimeFactors.eval_factors (a: ℕ) (ha: a ≠ 0) : eval (factors a) = a := by apply factors_eval'; assumption

end Nat
