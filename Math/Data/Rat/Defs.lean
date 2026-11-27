module

public import Math.Algebra.Field.Defs.Basic

namespace Math

-- a fraction is a non-reduced rational
public structure Fraction where
  num: ℤ
  den: ℕ
  den_pos: 0 < den

public structure Rational extends Fraction where
  ofFract ::
  reduced: num.gcd den = 1

notation "ℚ" => Rational

namespace Rational

def mk (q: Fraction) : Rational :=
  let r := q.num.gcd q.den
  {
    num := q.num / r
    den := q.den / r
    den_pos := by
      apply Nat.div_gcd_pos_of_pos_right
      exact q.den_pos
    reduced := by
      rw [Int.natCast_ediv, Int.gcd_ediv, Int.natAbs_natCast]
      unfold r; apply Nat.div_self
      apply Nat.gcd_pos_of_pos_right
      rw [Int.natAbs_natCast]; exact q.den_pos
      apply Int.gcd_dvd_left
      apply Int.gcd_dvd_right
  }

#axiom_blame mk
#print axioms mk

end Rational
