module

public import Math.Algebra.Semiring.Prime.Defs
import Math.Data.Nat.Find

open Math

namespace Nat

public inductive Classify (n: ℕ) where
| prime : IsPrime n -> Classify n
| composite : IsComposite n -> Classify n
| unit : IsUnit n -> Classify n

public theorem unit_iff_eq_one : IsUnit n ↔ n = 1 := by
  apply Iff.intro
  intro ⟨u, hu⟩
  have := u.val_mul_inv; rw [hu] at this
  exact Nat.eq_one_of_mul_eq_one_right this
  intro rfl; infer_instance

theorem minFactor_exists (n: ℕ) : ∃i, 1 < i ∧ i ∣ (n + 2) := by
  exists n + 2
  apply And.intro
  apply Nat.succ_lt_succ; apply Nat.zero_lt_succ
  apply dvd_refl

public def minFactor (n: ℕ) : ℕ :=
  match n with
  | 0 => 2
  | 1 => 1
  | n + 2 =>
    let k := n + 2
    Nat.findP (P := fun i => 1 < i ∧ i ∣ k) (minFactor_exists n)

public theorem minFactor_dvd (n: ℕ) : n.minFactor ∣ n := by
  match n with
  | 0 => apply dvd_zero
  | 1 => apply dvd_refl
  | n + 2 =>
    apply (Nat.findP_spec n.minFactor_exists).right

public theorem minFactor_min (n: ℕ) : ∀i, i ∣ n -> 1 < i -> n.minFactor ≤ i := by
  intro i i_dvd_n hi
  match n with
  | 0 =>
    match i with
    | i + 2 => apply Nat.le_add_left
  | 1 =>
    cases Nat.dvd_one.mp i_dvd_n
    apply Nat.le_refl
  | n + 2 =>
    apply Nat.le_of_not_lt (Nat.of_lt_findP n.minFactor_exists i · ?_)
    apply And.intro hi
    assumption

-- public theorem minFactor_prime (n: ℕ) (hn: n ≠ 1) : IsPrime n.minFactor where
--   not_unit := by
--     rw [unit_iff_eq_one]
--     match n with
--     | 0 => nofun
--     | n + 2 =>
--       intro h
--       have := (Nat.findP_spec (Nat.minFactor_exists n)).left
--       rw (occs := [1]) [←h] at this
--       nomatch Nat.lt_irrefl _ this
--   dvd_of_dvd_mul a b h := by
--     sorry
