module

import Math.Tactic.TypeStar
import Math.Tactic.AxiomBlame

namespace Nat

section

variable (f: ℕ -> Bool) (h: ∃i, f i)

structure findMeasure (h: ∃i, f i) where
  ofNat ::
  toNat : ℕ
  spec : ∀i < toNat, ¬f i

theorem lt_of_sub_pos' {n m : ℕ} (h : 0 < n - m) : m < n := by
  induction n generalizing m with
  | zero => rw [Nat.zero_sub] at h; nomatch h
  | succ n ih =>
    cases m with
    | zero => apply Nat.zero_lt_succ
    | succ m =>
      apply Nat.succ_lt_succ; apply ih
      rwa [Nat.succ_sub_succ] at h

theorem sub_lt_sub_left' {k m n : ℕ} : k < m → k < n → m - n < m - k := by
  intro k_lt_m k_lt_n
  induction k generalizing n m with
  | zero =>
    rw [Nat.sub_zero]
    cases n with
    | zero => contradiction
    | succ n =>
      cases m with
    | zero => contradiction
    | succ m =>
      rw [Nat.succ_sub_succ]
      apply Nat.lt_succ_of_le
      apply Nat.sub_le
  | succ k ih =>
    cases m with
    | zero => contradiction
    | succ m =>
    cases n with
    | zero => contradiction
    | succ n =>
    rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
    apply ih
    apply Nat.lt_of_succ_lt_succ; assumption
    apply Nat.lt_of_succ_lt_succ; assumption

instance : WellFoundedRelation (findMeasure f h) where
  rel a b := b.toNat < a.toNat
  wf := by
    obtain ⟨i, hi⟩ := h
    apply WellFounded.intro
    intro ⟨a, ha⟩
    induction h:i - a using Nat.strongRecOn generalizing a with
    | _ d ih =>
      cases d with
      | zero =>
        have := Nat.le_of_not_lt (ha i · hi)
        cases Nat.le_antisymm (Nat.le_of_sub_eq_zero h) this
        apply Acc.intro
        intro ⟨b, hb⟩ h
        dsimp at h
        nomatch hb i h hi
      | succ d =>
        apply Acc.intro
        intro ⟨b, hb⟩ g; dsimp at g
        apply ih _ _ _ _ rfl
        rw [←h]
        apply Nat.sub_lt_sub_left' _ g
        apply Nat.lt_of_sub_pos'
        rw [h]; apply Nat.zero_lt_succ

def findAux (i: ℕ) (hi: ∀j < i, ¬f j) : { i: ℕ // f i ∧ ∀j < i, ¬ f j } :=
  have := h
  if fi:f i then ⟨i, fi, hi⟩  else findAux (i + 1) <| by
    intro j hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
    apply hi; assumption; subst i; assumption
termination_by findMeasure.ofNat (h := h) i hi
decreasing_by
  apply Nat.lt_succ_of_le
  apply Nat.le_refl

variable {f: ℕ -> Bool} (h: ∃i, f i)

public def find : ℕ := findAux f h 0 nofun
public theorem find_spec : f (find h) := (findAux f h 0 nofun).property.left
public theorem of_lt_find : ∀i < find h, ¬f i := (findAux f h 0 nofun).property.right

variable {P: ℕ -> Prop} [DecidablePred P] (h: ∃i, P i)

def findPAux : { i: ℕ // P i ∧ ∀j < i, ¬ P j } :=
  let x := findAux (fun i => decide (P i)) (by
    obtain ⟨i, hi⟩ := h; exists i
    apply decide_eq_true; assumption) 0 nofun
  {
    val := x.val
    property := by
      obtain ⟨h, g⟩ := x.property
      apply And.intro
      exact of_decide_eq_true h
      intro j hj pj; apply g j hj
      apply decide_eq_true
      assumption
  }
public def findP : ℕ := findPAux h
public theorem findP_spec : P (findP h) := (findPAux h).property.left
public theorem of_lt_findP : ∀i < findP h, ¬P i := (findPAux h).property.right

end
