module

public import Math.Algebra.AddMonoidWithOne.Defs.Lemmas
public import Math.Algebra.Semiring.Defs.Basic

import Math.Algebra.Semiring.Defs.Hom

namespace Math

variable [SemiringOps α] [IsSemiring α]

public theorem natCast_pown (n m: ℕ) : (n ^ m: ℕ) = (n: α) ^ m :=
  map_pown (f := RingHom.natCast) _ _

public theorem two_mul (a: α) : (2: ℕ) * a = a + a := by
  rw [←nsmul_eq_natCast_mul, succ_nsmul, one_nsmul]

public theorem add_sq (a b: α) [IsCommAt a b] : (a + b) ^ 2 = a ^ 2 + (2: ℕ) * (a * b) + b ^ 2 := by
  rw [pown_succ, pown_one, mul_add, add_mul, add_mul, mul_comm b,
    ←add_assoc, add_assoc (a * a), ←two_mul, ←pown_two, ←pown_two]

public instance (n: ℕ) (a: α) : IsCommAt (n: α) a where
  mul_comm := by rw [←nsmul_eq_mul_natCast, ←nsmul_eq_natCast_mul]
