import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Semiring.Char
import LeanMath.Data.Rational.Defs

class RatCast (α: Type*) where
  protected ratCast : ℚ -> α

@[coe]
def Rational.cast [RatCast α] : ℚ -> α := RatCast.ratCast

@[coe]
def Rational.Fract.cast [RatCast α] : Fract -> α :=
  Rational.cast ∘ Rational.mk

instance {α} [RatCast α] : Coe ℚ α where
  coe := Rational.cast

instance [RatCast α] : Coe Rational.Fract α where
  coe := Rational.Fract.cast

class IsLawfulRatCast (α: Type*) [FieldOps α] [IsField α] [RatCast α] extends HasChar α 0 where
  protected ratCast_def (q: ℚ) : (q: α) = (q.num: α) /? (q.den: α)

def ratCast_def [FieldOps α] [IsField α] [RatCast α] [IsLawfulRatCast α] (q: ℚ) : (q: α) = (q.num: α) /? (q.den: α) :=
  IsLawfulRatCast.ratCast_def _

class IsChar0Field (α: Type*) [FieldOps α] [RatCast α] extends IsField α, IsLawfulRatCast α where

instance : RatCast ℚ where
  ratCast := id

instance : IsChar0Field ℚ where
  ratCast_def a := by
    simp [←Rational.mk_intCast, ←Rational.mk_natCast]
    rw [div?_eq_mul_inv?, Rational.mk_inv?, Rational.mk_mul]
    rw (occs := [1]) [←Rational.mk_toFract a]
    apply Rational.sound
    show _ = _
    simp
    rw [Int.sign_natCast_of_ne_zero, mul_one]
    exact a.den_ne_zero

def ratCastHom [FieldOps α] [RatCast α] [IsChar0Field α] : ℚ →+* α where
  toFun := Rational.cast
  map_zero := by
    rw [ratCast_def]
    show ((0: ℤ): α) /? ((1: ℕ): α) = _
    simp [intCast_zero, natCast_one, div?_one]
  map_one := by
    rw [ratCast_def]
    show ((1: ℤ): α) /? ((1: ℕ): α) = _
    simp [intCast_one, natCast_one, div?_one]
  map_add a b := by
    rw [ratCast_def, ratCast_def, ratCast_def]
    rw [div?_add_div?]
    rw [
      show ((a + b).num: α) /? ((a + b).den: α) =
      ((a.num * b.den + b.num * a.den: ℤ): α) /? ((a.den * b.den): α)~(?_) from ?_
    ]
    · congr
      rw [intCast_add, intCast_mul, intCast_mul, intCast_ofNat, intCast_ofNat]
    · rw [←natCast_mul]
      apply natCast_ne_zero
      intro h
      rcases (of_mul_eq_zero h) with h | h
      exact a.den_ne_zero h
      exact b.den_ne_zero h
    conv => {
      lhs
      simp [HAdd.hAdd]
      simp [Add.add, Rational.lift₂, Rational.mk]
    }
    rw [intCast_div?_intCast (hm := by
      rw [intCast_ofNat]
      intro h; rw [←natCast_zero] at h
      replace h := HasChar.natCast_inj h
      replace h := Int.gcd_eq_zero_iff.mp h
      rw [←natCast_mul, ←natCast_zero] at h
      replace h := HasChar.natCast_inj h.right
      rcases of_mul_eq_zero h with h | h
      exact a.den_ne_zero h
      exact b.den_ne_zero h) _ _ (by
      apply Int.gcd_dvd_left)]
    conv => {
      lhs; arg 1; arg 2
      rw [intCast_ofNat]
    }
    conv => {
      lhs; arg 2
      rw [natCast_div?_natCast (hm := by
        intro h; rw [←natCast_zero] at h
        replace h := HasChar.natCast_inj h
        replace h := Int.gcd_eq_zero_iff.mp h
        rw [←natCast_mul, ←natCast_zero] at h
        replace h := HasChar.natCast_inj h.right
        rcases of_mul_eq_zero h with h | h
        exact a.den_ne_zero h
        exact b.den_ne_zero h) _ _ (by
          rw [←natCast_mul, ←Int.natCast_dvd_natCast']
          apply Int.gcd_dvd_right)]
    }
    simp [div?_eq_mul_inv?, inv?_mul_rev, inv?_inv?]
    rw [mul_assoc, ←mul_assoc (_⁻¹?~(_)), inv?_mul_cancel, one_mul,
      ←inv?_mul_rev]
    congr 2
    rw [natCast_mul]
    rw [←natCast_mul]
    intro h; rw [←natCast_zero] at h
    replace h := HasChar.natCast_inj h
    rcases of_mul_eq_zero h with h | h
    exact a.den_ne_zero h
    exact b.den_ne_zero h
  map_mul a b := by
    rw [ratCast_def, ratCast_def, ratCast_def]
    conv => {
      lhs
      simp [HMul.hMul]
      simp [Mul.mul, Rational.lift₂, Rational.mk]
    }
    rw [intCast_div?_intCast (hm := by
      rw [intCast_ofNat]
      intro h; rw [←natCast_zero] at h
      replace h := HasChar.natCast_inj h
      replace h := Int.gcd_eq_zero_iff.mp h
      rw [←natCast_mul, ←natCast_zero] at h
      replace h := HasChar.natCast_inj h.right
      rcases of_mul_eq_zero h with h | h
      exact a.den_ne_zero h
      exact b.den_ne_zero h) _ _ (by
      apply Int.gcd_dvd_left)]
    conv => {
      lhs; arg 1; arg 2
      rw [intCast_ofNat]
    }
    conv => {
      lhs; arg 2
      rw [natCast_div?_natCast (hm := by
        intro h; rw [←natCast_zero] at h
        replace h := HasChar.natCast_inj h
        replace h := Int.gcd_eq_zero_iff.mp h
        rw [←natCast_mul, ←natCast_zero] at h
        replace h := HasChar.natCast_inj h.right
        rcases of_mul_eq_zero h with h | h
        exact a.den_ne_zero h
        exact b.den_ne_zero h) _ _ (by
          rw [←natCast_mul, ←Int.natCast_dvd_natCast']
          apply Int.gcd_dvd_right)]
    }
    simp [div?_eq_mul_inv?, inv?_mul_rev, inv?_inv?]
    rw [mul_assoc, ←mul_assoc (_⁻¹?~(_)), inv?_mul_cancel, one_mul]
    rw [mul_assoc, mul_left_comm  _ (Int.cast b.num), ←mul_assoc]
    congr 2
    rw [intCast_mul]
    rw [←inv?_mul_rev]
    congr 1
    rw [natCast_mul, mul_comm]
    intro h; rw [←natCast_mul, ←natCast_zero] at h
    replace h := HasChar.natCast_inj h
    rcases of_mul_eq_zero h with h | h
    exact b.den_ne_zero h
    exact a.den_ne_zero h

def ratCast_zero [FieldOps α] [RatCast α] [IsChar0Field α] : Rational.cast 0 = (0: α) :=
  map_zero (ratCastHom (α := α))
def ratCast_one [FieldOps α] [RatCast α] [IsChar0Field α] : Rational.cast 1 = (1: α) :=
  map_one (ratCastHom (α := α))
def ratCast_add [FieldOps α] [RatCast α] [IsChar0Field α] (a b: ℚ) : Rational.cast (a + b) = (a + b: α) :=
  map_add (ratCastHom (α := α)) _ _
def ratCast_mul [FieldOps α] [RatCast α] [IsChar0Field α] (a b: ℚ) : Rational.cast (a * b) = (a * b: α) :=
  map_mul (ratCastHom (α := α)) _ _
