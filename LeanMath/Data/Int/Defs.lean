import LeanMath.Tactic.TypeStar

@[cases_eliminator]
def Int.coe_cases (motive: ℤ -> Sort*) (ofNat: ∀a: ℕ, motive a) (negSucc: ∀a, motive (Int.negSucc a)) : ∀z, motive z
| .ofNat _ => ofNat _
| .negSucc _ => negSucc _

def Int.succ_pred_induction {motive: ℤ -> Prop}
  (zero: motive 0)
  (succ: ∀n, motive n -> motive (n + 1))
  (pred: ∀n, motive n -> motive (n - 1)) : ∀z, motive z := by
  intro z
  cases z <;> rename_i z
  · induction z with
    | zero => apply zero
    | succ n ih => apply succ n ih
  · induction z with
    | zero => apply pred 0 zero
    | succ n ih => apply pred (Int.negSucc n) ih

def Int.natCast_dvd_natCast' {a b: ℕ} : (a: ℤ) ∣ b ↔ a ∣ b := by
  apply Iff.intro
  · intro ⟨k, ha⟩
    cases k with
    | negSucc k =>
      rw [Int.ofNat_mul_negSucc] at ha
      match a with
      | a + 1 =>
        have := Int.natCast_nonneg b
        rw [ha] at this
        contradiction
      | 0 =>
        rw [Nat.zero_mul, Int.natCast_zero, Int.neg_zero] at ha
        cases Int.ofNat.inj ha
        apply Nat.dvd_refl
    | ofNat k =>
      rw [←natCast_mul] at ha
      cases Int.ofNat.inj ha
      apply Nat.dvd_mul_right
  · intro ⟨k, h⟩
    exists k
    rw [←natCast_mul]; congr
