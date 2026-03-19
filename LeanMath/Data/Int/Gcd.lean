import LeanMath.Data.Nat.Gcd

namespace Int

def gcdA (a b: ℤ) : ℤ :=
  a.sign * Nat.gcdA a.natAbs b.natAbs
def gcdB (a b: ℤ) : ℤ :=
  b.sign * Nat.gcdB a.natAbs b.natAbs

def bezout (a b: ℤ) : gcd a b = a * gcdA a b + b * gcdB a b := by
  unfold gcd gcdA gcdB
  rw [←Int.mul_assoc, ←Int.mul_assoc,
    Int.mul_sign_self, Int.mul_sign_self]
  apply Nat.bezout

end Int
