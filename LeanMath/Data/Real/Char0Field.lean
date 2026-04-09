import LeanMath.Algebra.Char0Field.Defs
import LeanMath.Data.Real.Defs

instance : RatCast ℝ where
  ratCast := Real.ofRat

instance [LEM] : IsChar0Field ℝ where
  ratCast_def q := by
    cases q using Rational.ind with | _ q =>
    rw [defaultRatCast_mk]
    show Real.ofRat (Rational.cast (Rational.mk q)) = _
    rw [ratCast_mk, map_div?]; congr 1
