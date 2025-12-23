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
