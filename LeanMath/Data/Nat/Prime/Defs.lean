import LeanMath.Data.Nat.Find
import LeanMath.Data.Nat.Basic
import LeanMath.Data.Nat.Gcd
import LeanMath.Data.Int.Defs
import LeanMath.Algebra.Dvd.Defs
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

private def semiprime_iff {n: ℕ} : (∀⦃x y: ℕ⦄, n ∣ x * y -> n ∣ x ∨ n ∣ y) ∧ n ≠ 0 ↔ ∀x, x ∣ n -> x = n ∨ x = 1 := by
  apply Iff.intro
  · intro ⟨irred, nz⟩ x hx
    obtain ⟨k, rfl⟩ := hx
    rcases irred (Nat.dvd_refl _) with h | h
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
    intro a b g
    rcases h (Nat.gcd n a) (Nat.gcd_dvd_left _ _) with h | h
    rw [←h]
    left; apply Nat.gcd_dvd_right
    right
    have := Nat.bezout n a
    rw [h, Int.natCast_one] at this
    apply Int.natCast_dvd_natCast'.mp
    rw [←Int.mul_one b]
    rw [this, Int.mul_add, Int.mul_left_comm, ←Int.mul_assoc b,
      Int.mul_comm b a]
    apply Int.dvd_add
    apply Int.dvd_mul_right
    apply flip Int.dvd_trans
    apply Int.dvd_mul_right
    rw [←Int.natCast_mul]
    apply Int.natCast_dvd_natCast'.mpr
    assumption

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
    apply (semiprime_iff.mpr _).left
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

end Nat
