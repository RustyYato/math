module

public import Math.Algebra.Module.Ring
public import Math.Algebra.Algebra.Defs.Basic
public import Math.Algebra.Ring.Defs.Hom

import Math.Algebra.Ring.Defs.Lemmas

namespace Math

public instance [RingOps R] [IsRing R] : AlgebraMap ℤ R where
  toRingHom := RingHom.intCast

public instance [RingOps R] [IsRing R] : IsAlgebra ℤ R where
  commutes r x := by
    show r * x = x * r
    rw [←zsmul_eq_intCast_mul, ←zsmul_eq_mul_intCast]
  smul_def a b := by rw [zsmul_eq_intCast_mul]; rfl
