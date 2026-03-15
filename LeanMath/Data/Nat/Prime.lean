import LeanMath.Data.Nat.Find
import LeanMath.Algebra.Dvd.Defs
import LeanMath.Data.DirectSum.Defs
import LeanMath.Tactic.AxiomBlame

namespace Nat

private def minFac_exists (n: ℕ) (hn: n ≠ 1) : ∃m, m ∣ n ∧ 1 < m :=
  match n with
  | 0 => ⟨2, Nat.dvd_zero _,  by decide⟩
  | _ + 2 => ⟨_, Nat.dvd_refl _,  Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩

def minFact (n: ℕ) :=
  match n with
  | 0 => 2 | 1 => 1
  | n + 2 => Nat.find (minFac_exists (n + 2) nofun)

def minFact_dvd (n: ℕ) : Nat.minFact n ∣ n := by
  match n with
  | 0 | 1 => decide
  | n + 2 =>
    have := Nat.find_spec (minFac_exists (n + 2) nofun)
    exact this.left

def irreducible_iff {n: ℕ} : IsIrreducible n ∧ n ≠ 0 ↔ ∀x, x ∣ n -> x = n ∨ x = 1 := by
  apply Iff.intro
  · intro ⟨irred, nz⟩ x hx
    obtain ⟨k, rfl⟩ := hx
    rcases irred rfl with h | h
    · left; apply Nat.dvd_antisymm
      apply Nat.dvd_mul_right
      assumption
    · right
      have := Nat.dvd_antisymm h (Nat.dvd_mul_left _ _)
      rw (occs := [2]) [←one_mul k] at this
      exact of_mul_right₀ (by
        intro rfl
        contradiction) this
  · intro h
    apply flip And.intro
    intro rfl
    have := h 2
    contradiction
    intro x y g
    rcases h x ⟨y, g⟩ <;> subst x
    left; rfl
    rw [one_mul] at g
    subst n
    right; rfl

def minFact_ne_zero (n: ℕ) : n.minFact ≠ 0 := by
  match n with
  | 0 | 1 => decide
  | n + 2 =>
    have := Nat.find_spec (minFac_exists (n + 2) nofun)
    apply Nat.ne_of_gt
    apply Nat.lt_trans _ this.right
    decide

def minFact_prime (n: ℕ) (hn: n ≠ 1) : IsPrime (Nat.minFact n) where
  irreducible := by
    apply (irreducible_iff.mpr _).left
    intro x hx
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero <| minFact_ne_zero _) hx
    replace  this := Or.symm (Nat.lt_or_eq_of_le this)
    rcases this with h | h
    left; assumption
    right
    match n with
    | 0 =>
      match x with
      | 1 => rfl
      | 0 => contradiction
    | n + 2 =>
      have := Nat.find_minimal (Nat.minFac_exists (n + 2) nofun) x h
      simp at this
      replace := this (Nat.dvd_trans hx (Nat.minFact_dvd _))
      match x with
      | 0 =>
        rw [Nat.zero_dvd] at hx
        rw [hx] at h
        contradiction
      | 1 =>
        rfl
  ne_zero := minFact_ne_zero _
  not_unit := by
    intro h
    obtain ⟨u, _ ⟩ := h
    cases Subsingleton.allEq u 1
    rename_i h; replace h : _ = 1 := h
    match n with
    | 0 => contradiction
    | n + 2 =>
      have : 1 < (n + 2).minFact := (Nat.find_spec (minFac_exists _ hn)).right
      rw [h] at this
      contradiction

def two_le_prime (n: ℕ) (h: IsPrime n) : 2 ≤ n := by
  match n with
  | 0 => nomatch h.ne_zero
  | 1 => nomatch h.not_unit inferInstance
  | n + 2 => apply Nat.le_add_left

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

def mul_lt_mul_left' {a b c : ℕ} : 0 < a → (a * b < a * c ↔ b < c) := by
  intro h
  cases a; contradiction; clear h
  rename_i a
  induction b generalizing c with
  | zero => simp
  | succ b ih =>
    cases c with
    | zero => simp
    | succ c =>
    rw [mul_succ, mul_succ]
    rw [Nat.add_lt_add_iff_right, Nat.succ_lt_succ_iff]
    apply ih

def div_lt_of_lt_mul' {m n k : ℕ} : m < n * k → m / n < k := by
  intro h
  rw [←Nat.div_add_mod m n] at h
  replace h : n * (m / n) < n * k := by
    apply Nat.lt_of_le_of_lt _ h
    apply Nat.le_add_right
  refine (Nat.mul_lt_mul_left' ?_).mp h
  apply Nat.pos_of_ne_zero
  intro rfl
  rw [zero_mul, zero_mul] at h
  contradiction

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
