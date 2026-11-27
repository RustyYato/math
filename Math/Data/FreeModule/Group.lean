module

public import Math.Data.FreeModule.Defs
public import Math.Algebra.Ring.Defs.Basic

namespace Math.FreeModule

variable [RingOps R] [IsRing R]

public instance  : SMul ℤ (FreeModule R α) where
  smul r a := (r: R) • a

public instance  : Neg (FreeModule R α) where
  neg a := (-1: ℤ) • a

public instance  : Sub (FreeModule R α) where
  sub a b := a + -b

public instance  : IsLawfulZSMul (FreeModule R α) where
  ofNat_zsmul a n := by
    show ((n: ℤ): R) • a = _
    rw [intCast_ofNat]; rfl
  negSucc_zsmul a n := by
    show ((Int.negSucc n): R) • a = ((-1: ℤ): R) • ((n + 1: ℕ): R) • _
    rw [intCast_negSucc, ←mul_smul, ←zsmul_eq_intCast_mul, neg_one_zsmul]
public instance  : IsAddGroup (FreeModule R α) where
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel a := by
    show ((-1: ℤ): R) • a + a = 0
    rw (occs := [2]) [←one_smul (R := R) a, ←intCast_one]
    rw [←add_smul, ←intCast_add, neg_add_cancel, intCast_zero, zero_smul]
