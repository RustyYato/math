module

public import Math.Data.FreeAlgebra.Defs
public import Math.Algebra.Algebra.Ring
public import Math.Algebra.Ring.Defs

namespace Math

section

variable {R α: Type*} [RingOps R] [IsRing R]

public instance : Neg (FreeAlgebra R α) where
  neg a := algebraMap R (-1) * a

public instance : IntCast (FreeAlgebra R α) where
  intCast n := algebraMap R n

public instance : RingOps (FreeAlgebra R α) where
  sub a b := a + -b
  toZSMul := ⟨fun n a => n * a⟩

public instance : IsLawfulIntCast (FreeAlgebra R α) where
  intCast_ofNat n := by
    show algebraMap R (n: ℤ) = algebraMap R n
    rw [intCast_ofNat]
  intCast_negSucc n := by
    show algebraMap R (Int.negSucc n) = algebraMap R (-1) * algebraMap R (n + 1: ℕ)
    rw [intCast_negSucc, ←map_mul, ←neg_mul_left, one_mul]

public instance : IsRing (FreeAlgebra R α) where
  neg_add_cancel a := by
    show algebraMap R (-1) * a + a = 0
    rw (occs := [2]) [←one_mul a]
    rw [show 1 * a = algebraMap R 1 * a by rw [map_one]]
    rw [←add_mul, ←map_add, neg_add_cancel, map_zero, zero_mul]
  sub_eq_add_neg _ _ := rfl
  ofNat_zsmul a n := by
    show (n: ℤ) * a = n * a
    rw [intCast_ofNat]
  negSucc_zsmul a n := by
    show (Int.negSucc n: ℤ) * a = -((n + 1: ℕ) * a)
    rw [intCast_negSucc]
    show algebraMap R (-1) * (n + 1: ℕ) * a = algebraMap R (-1) * ((n + 1: ℕ) * a)
    rw [mul_assoc]

end

public abbrev FreeRing (α: Type*) := FreeAlgebra ℤ α
