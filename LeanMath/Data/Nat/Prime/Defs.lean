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

def one_lt_prime (p: ℕ) (hp: IsPrime p) : 1 < p := by
  match p with
  | 0 => have := hp.ne_zero; contradiction
  | 1 => have := hp.not_unit inferInstance; contradiction
  | n + 2 =>
    apply Nat.succ_lt_succ
    apply Nat.zero_lt_succ

def minFact_minimal (n: ℕ) : ∀p, 1 < p -> p ∣ n -> Nat.minFact n ≤ p := by
  match n with
  | 0 =>
    intro p hp h; clear h
    show 2 ≤ p
    apply Nat.succ_le_of_lt
    assumption
  | 1 =>
    intro p hp h
    rw [Nat.dvd_one] at h
    subst h
    apply Nat.le_refl
  | n + 2 =>
    intro p hp h
    refine Nat.not_lt.mp <| (Nat.find_minimal (minFac_exists (n + 2) nofun) p · ⟨?_, ?_⟩)
    assumption
    assumption

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

def prime_def {p: ℕ} (hp: IsPrime p) : ∀x, x ∣ p -> x = p ∨ x = 1 := by
  rw [←semiprime_iff]
  apply And.intro
  apply hp.irreducible
  exact hp.ne_zero

def minFact_ne_zero (n: ℕ) : n.minFact ≠ 0 := by
  match n with
  | 0 | 1 => decide
  | n + 2 =>
    have := Nat.find_spec (minFac_exists (n + 2) nofun)
    apply Nat.ne_of_gt
    apply Nat.lt_trans _ this.right
    decide

@[reducible]
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

instance : IsPrime (Nat.minFact 0) := minFact_prime _ nofun
instance : IsPrime (Nat.minFact (n + 2)) := minFact_prime _ nofun

def two_le_prime (n: ℕ) (h: IsPrime n) : 2 ≤ n := by
  match n with
  | 0 => nomatch h.ne_zero
  | 1 => nomatch h.not_unit inferInstance
  | n + 2 => apply Nat.le_add_left

def minFact_eq_of_minimal (n: ℕ) : ∀p, 1 < p -> p ∣ n -> (∀m, IsPrime m -> m ∣ n -> p ≤ m) -> Nat.minFact n = p := by
  intro p pnontriv hp gp
  apply Nat.le_antisymm
  · apply minFact_minimal
    assumption
    assumption
  · apply gp
    · apply Nat.minFact_prime
      intro rfl
      rw [Nat.dvd_one] at hp
      subst p
      contradiction
    apply Nat.minFact_dvd

inductive Classify : ℕ -> Type where
| unit : Classify 1
| prime (p: ℕ) : IsPrime p -> Classify p
| composite (c: ℕ) : IsComposite c -> Classify c
deriving Repr

instance : Subsingleton (Classify n) where
  allEq := by
    intro a b
    have : ¬IsPrime (1: ℕ) := fun p => p.not_unit inferInstance
    have : ¬IsComposite (1: ℕ) := fun c => c.not_unit inferInstance
    cases a <;> cases b
    any_goals rfl
    any_goals contradiction
    iterate 2
    rename IsPrime n => hp
    have := hp.not_composite
    contradiction

instance : DecidableEq (Classify n) :=
  fun _ _ => .isTrue (Subsingleton.allEq _ _)

def classify (n: ℕ) : Classify n :=
  if h₀:n = 1 then
    h₀ ▸ .unit
  else
    let p := n.minFact
    if h₁:p = n then
      .prime n (by
        rw [←h₁]
        apply minFact_prime
        assumption)
    else
        Classify.composite n <| by
          have := Nat.mul_div_cancel' (n := p) (m := n) (Nat.minFact_dvd _)
          refine ⟨p, n / p, ?_, ?_, this⟩
          · intro h
            have := minFact_prime n h₀
            apply IsPrime.not_unit (α := ℕ) (a := n.minFact)
            assumption
          · intro h
            rw [Nat.is_unit_iff] at h
            rw [h, Nat.mul_one] at this
            contradiction

def is_prime (n: ℕ) : Bool :=
  match classify n with
  | .prime _ _ => true
  | .unit | .composite _ _ => false

def is_composite (n: ℕ) : Bool :=
  match classify n with
  | .composite _ _ => true
  | .unit | .prime _ _ => false

instance (n: ℕ) : Decidable (IsPrime n) :=
  decidable_of_bool n.is_prime <| by
    unfold is_prime
    cases classify n <;> dsimp
    apply Iff.intro nofun
    intro h; nomatch h.not_unit inferInstance
    apply Iff.intro <;> (intro; trivial)
    apply Iff.intro nofun
    intro h; exfalso; apply h.not_composite
    assumption

instance (n: ℕ) : Decidable (IsComposite n) :=
  decidable_of_bool n.is_composite <| by
    unfold is_composite
    cases classify n <;> dsimp
    apply Iff.intro nofun
    intro h; nomatch h.not_unit inferInstance
    apply Iff.intro nofun
    rename_i h; intro; exfalso
    apply h.not_composite; assumption
    apply Iff.intro <;> (intro; trivial)

end Nat
