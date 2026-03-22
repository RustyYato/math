import LeanMath.Data.Nat.Prime.Defs
import LeanMath.Data.DirectSum.Defs

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

private def existsFactor (n: ℕ) (hn: n ≠ 0) : ∃k, n.minFact ^ (n - k) ∣ n := by
  exists (n - 1)
  rw [Nat.sub_sub_eq_min, Nat.min_eq_right, npow_one]
  apply Nat.minFact_dvd
  apply Nat.succ_le_of_lt
  apply Nat.pos_of_ne_zero
  assumption

private def find_lt_existsFactor (n: ℕ) (hn: n ≠ 0) : Nat.find (existsFactor n hn) < n := by
  apply Nat.not_le.mp
  intro h; rw [Nat.le_iff_lt_or_eq] at h
  rcases h with h | h
  · have := Nat.find_minimal _ _ h
    rw [Nat.sub_self, npow_zero] at this
    exact this (Nat.one_dvd _)
  · have := Nat.find_minimal (existsFactor n hn) (n - 1) ?_
    rw [Nat.sub_sub_self, npow_one] at this
    exact this (Nat.minFact_dvd _)
    apply Nat.succ_le_of_lt
    apply Nat.pos_of_ne_zero
    assumption
    rw [←h]
    match n with
    | n + 1 =>
    apply Nat.lt_succ_self

def factors_rec_lemma (n: ℕ) (hn: 1 < n) : n / (Nat.minFact n) ^ (n - Nat.find (existsFactor n (Nat.ne_zero_of_lt hn))) < n := by
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
  n / Nat.minFact n ^ (n - Nat.find (existsFactor n (Nat.ne_zero_of_lt h))) ≠ 0 := by
  let hex := existsFactor n (Nat.ne_zero_of_lt h)
  have : Nat.minFact n ^ (n - Nat.find hex) ∣ n := Nat.find_spec hex
  replace := Nat.mul_div_cancel_left' this
  intro h; rw [h, mul_zero] at this
  subst n; contradiction

def factors (n: ℕ) : PrimeFactors :=
  if h₁:1 < n then
    let m := n.minFact
    have existsFactor : ∃k, m ^ (n - k) ∣ n := by
      exists (n - 1)
      rw [Nat.sub_sub_eq_min, Nat.min_eq_right, npow_one]
      apply Nat.minFact_dvd
      apply Nat.succ_le_of_lt
      apply Nat.pos_of_ne_zero
      apply Nat.ne_zero_of_lt
      assumption
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

def factors_one : factors 1 = 1 := by
  unfold factors
  rw [dif_neg]
  apply Nat.lt_irrefl

def factors_mul (a b: ℕ) (ha: a ≠ 0) (hb: b ≠ 0) : factors (a * b) = factors a * factors b := by
  sorry

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
  | prime p hp =>
    have minFact_eq_self : p.minFact = p := by
      rcases prime_def hp p.minFact (Nat.minFact_dvd p) with h | h
      assumption
      have := (minFact_prime p ?_).not_unit (h ▸ inferInstance)
      contradiction
      intro rfl
      exact hp.not_unit inferInstance
    have pow_eq_one : p - Nat.find (existsFactor p hp.ne_zero) = 1 := by
      have h := find_spec (existsFactor p hp.ne_zero)
      rw (occs := [1]) [minFact_eq_self] at h
      replace h := prime_def hp _ h
      rcases h with h | h
      · rwa [Nat.pow_eq_self_iff] at h
        · apply one_lt_prime
          assumption
      · rw [Nat.pow_eq_one] at h
        rcases h with h | h
        subst p; nomatch hp.not_unit inferInstance
        rw [Nat.sub_eq_zero_iff_le] at h
        have := Nat.not_le_of_gt (find_lt_existsFactor p hp.ne_zero) h
        contradiction
    rw [PrimeFactors.eval'_of_prime]
    unfold factors
    dsimp; rw [dif_pos (by
      apply one_lt_prime
      assumption)]
    rw [←mul_one (PrimeFactors.of_prime p hp)]; congr
    rw [show find (existsFactor p hp.ne_zero) = p - 1 from ?_]
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

def PrimeFactors.eval : PrimeFactors ↪* ℕ where
  toGroupHom := PrimeFactors.eval'
  inj := by
    intro a b h
    replace h : eval' a = eval' b := h
    have := eval'_factors b
    rwa [←h, eval'_factors] at this

end Nat
