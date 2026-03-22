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

def eval : PrimeFactors →* ℕ where
  toFun := preEval
  map_one := by
    show AddOfMul.get (DirectSum.lift _ 0) = _
    rw [map_zero]; rfl
  map_mul a b := by
    show AddOfMul.get (DirectSum.lift _ (_ + _)) = _
    rw [map_add]; rfl

def eval_of_prime : eval (of_prime p hp) = p := by
  show AddOfMul.get (DirectSum.lift _ (DirectSum.ι _ _)) = _
  rw [DirectSum.lift_ι]
  show p ^ 1 = p
  rw [npow_succ, npow_zero, one_mul]

end PrimeFactors

private def one_lt_prime (p: ℕ) (hp: IsPrime p) : 1 < p := by
  match p with
  | 0 => have := hp.ne_zero; contradiction
  | 1 => have := hp.not_unit inferInstance; contradiction
  | n + 2 =>
    apply Nat.succ_lt_succ
    apply Nat.zero_lt_succ

private def existsFactor (n: ℕ) (hn: n ≠ 0) : ∃k, n.minFact ^ (n - k) ∣ n := by
  exists (n - 1)
  rw [Nat.sub_sub_eq_min, Nat.min_eq_right, npow_one]
  apply Nat.minFact_dvd
  apply Nat.succ_le_of_lt
  apply Nat.pos_of_ne_zero
  assumption

def factors_rec_lemma (n: ℕ) (hn: 1 < n) : n / (Nat.minFact n) ^ (n - Nat.find (existsFactor n (Nat.ne_zero_of_lt hn))) < n := by
  have npos := Nat.zero_lt_of_lt hn
  have n_ne_zero := Nat.ne_zero_of_lt hn
  apply div_lt_of_lt_mul'
  rw (occs := [1]) [←Nat.one_mul n]
  apply Nat.mul_lt_mul_of_pos_right _ npos
  apply Nat.one_lt_pow
  · intro h
    have g₀ := Nat.sub_eq_zero_iff_le.mp h
    have g₁ := Nat.not_lt.mp (Nat.find_minimal (existsFactor _ n_ne_zero) n · (by
      rw [Nat.sub_self, Nat.pow_zero]; apply Nat.one_dvd))
    have := Nat.le_antisymm g₀ g₁

    have := Nat.find_minimal (existsFactor _ n_ne_zero) (n -1) (by
      rw [←this]
      apply Nat.pred_lt
      assumption)
    rw [Nat.sub_sub_self, Nat.pow_one] at this
    apply this
    apply Nat.minFact_dvd
    apply Nat.succ_le_of_lt
    apply Nat.pos_of_ne_zero
    assumption
  · apply one_lt_prime
    apply Nat.minFact_prime
    intro rfl; contradiction

def factors (n: ℕ) (hn: n ≠ 0) : PrimeFactors :=
  if h₁:n = 1 then
    1
  else
    let m := n.minFact
    have existsFactor : ∃k, m ^ (n - k) ∣ n := by
      exists (n - 1)
      rw [Nat.sub_sub_eq_min, Nat.min_eq_right, npow_one]
      apply Nat.minFact_dvd
      apply Nat.succ_le_of_lt
      apply Nat.pos_of_ne_zero
      assumption
    let k := n - Nat.find existsFactor
    PrimeFactors.of_prime m (n.minFact_prime h₁) ^ k * (
      (n / (m ^ k)).factors <| by
        show n / m ^ k ≠ 0
        have : m ^ k ∣ n := Nat.find_spec existsFactor
        replace := Nat.mul_div_cancel_left' this
        intro h; rw [h, mul_zero] at this
        subst n; contradiction
    )
decreasing_by
  apply factors_rec_lemma
  match n with
  | n + 2 =>
  apply Nat.succ_lt_succ
  apply Nat.zero_lt_succ

def factors_eval (n: ℕ) (hn: n ≠ 0) : PrimeFactors.eval (n.factors hn) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  unfold factors
  split; subst n; rw [map_one]
  dsimp; rw [map_mul,
    map_npow,
    PrimeFactors.eval_of_prime, ih]
  rw [Nat.mul_div_cancel']

  have (h: ∃ k, n.minFact ^ (n - k) ∣ n) : n.minFact ^ (n - Nat.find h) ∣ n := Nat.find_spec h
  apply this

  apply factors_rec_lemma
  match n with
  | n + 2 =>
  apply Nat.succ_lt_succ
  apply Nat.zero_lt_succ

end Nat
