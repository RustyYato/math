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

private def simple_factors_rec_lemma (n: ℕ) (h: 1 < n) : n / n.minFact < n := by
  apply div_lt_of_lt_mul'
  apply flip Nat.lt_of_lt_of_le
  apply Nat.mul_le_mul_right
  apply two_le_prime
  refine Nat.minFact_prime _ ?_
  intro rfl; contradiction
  rw (occs := [1]) [←one_mul n]
  apply Nat.mul_lt_mul_of_pos_right
  decide
  apply Nat.pos_of_ne_zero
  intro rfl; contradiction

private def simple_factors (n: ℕ) (hn: n ≠ 0) : PrimeFactors :=
  if h₁:n = 1 then
    1
  else
    let m := n.minFact
    PrimeFactors.of_prime m (n.minFact_prime h₁) * (
      (n / m).simple_factors <| by
        show n / n.minFact ≠ 0
        have ⟨k, hk⟩ := n.minFact_dvd
        rw (occs := [1]) [hk]
        rw [Nat.mul_div_cancel_left]
        intro rfl
        rw [mul_zero] at hk
        contradiction
        apply Nat.pos_of_ne_zero
        apply Nat.minFact_ne_zero
    )
decreasing_by
  apply simple_factors_rec_lemma
  match n with
  | n + 2 =>
  apply Nat.succ_lt_succ
  apply Nat.zero_lt_succ

private def simple_factors_eval' (n: ℕ) (hn: n ≠ 0) : PrimeFactors.eval' (n.simple_factors hn) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  unfold simple_factors
  split; subst n; rw [map_one]
  dsimp; rw [map_mul, PrimeFactors.eval'_of_prime, ih]
  rw [Nat.mul_div_cancel']
  apply Nat.minFact_dvd
  apply simple_factors_rec_lemma
  match n with
  | n + 2 =>
  apply Nat.succ_lt_succ
  apply Nat.zero_lt_succ

-- def factors (n: ℕ) (hn: n ≠ 0) : PrimeFactors :=
--   if h₁:n = 1 then
--     1
--   else
--     let m := n.minFact
--     have existsFactor : ∃k, m ^ (n - k) ∣ n := by
--       exists (n - 1)
--       rw [Nat.sub_sub_eq_min, Nat.min_eq_right, npow_one]
--       apply Nat.minFact_dvd
--       apply Nat.succ_le_of_lt
--       apply Nat.pos_of_ne_zero
--       assumption
--     let k := n - Nat.find existsFactor
--     PrimeFactors.of_prime m (n.minFact_prime h₁) ^ k * (
--       (n / (m ^ k)).factors <| by
--         show n / (n.minFact ^ k) ≠ 0
--         sorry
--         -- have ⟨k, hk⟩ := n.minFact_dvd
--         -- rw (occs := [1]) [hk]
--         -- rw [Nat.mul_div_cancel_left]
--         -- intro rfl
--         -- rw [mul_zero] at hk
--         -- contradiction
--         -- apply Nat.pos_of_ne_zero
--         -- apply Nat.minFact_ne_zero
--     )
-- decreasing_by
--   sorry
--   -- apply div_lt_of_lt_mul'
--   -- apply flip Nat.lt_of_lt_of_le
--   -- apply Nat.mul_le_mul_right
--   -- apply two_le_prime
--   -- exact Nat.minFact_prime _ h₁
--   -- rw (occs := [1]) [←one_mul n]
--   -- apply Nat.mul_lt_mul_of_pos_right
--   -- decide
--   -- apply Nat.pos_of_ne_zero
--   -- assumption

-- #axiom_blame factors

end Nat
