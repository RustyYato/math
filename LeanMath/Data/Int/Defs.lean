import LeanMath.Tactic.TypeStar

@[cases_eliminator]
def Int.coe_cases (motive: ℤ -> Sort*) (ofNat: ∀a: ℕ, motive a) (negSucc: ∀a, motive (Int.negSucc a)) : ∀z, motive z
| .ofNat _ => ofNat _
| .negSucc _ => negSucc _
