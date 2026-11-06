module

import Math.Tactic.Basic

namespace Math

@[cases_eliminator]
public def Int.cases {motive: ℤ -> Sort u} (ofNat: ∀n: ℕ, motive n) (negSucc: ∀n, motive (Int.negSucc n)) : ∀z, motive z
| .ofNat n => ofNat n
| .negSucc n => negSucc n
