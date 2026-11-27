module

public import Math.Algebra.Semiring.Defs.Hom
public import Math.Algebra.AddGroupWithOne.Defs.Hom
public import Math.Algebra.Ring.Defs.Basic

import Math.Algebra.Ring.Defs.Lemmas

namespace Math

variable [RingOps α] [IsRing α]

@[expose] public def RingHom.intCast : ℤ →+* α where
  toFun := Int.cast
  map_zero := by exact intCast_zero
  map_one := by exact intCast_one
  map_add := by exact intCast_add
  map_mul := by exact intCast_mul

@[simp] public theorem RingHom.apply_intCast (n: ℤ) : RingHom.intCast n = (n: α) := rfl

public instance : Subsingleton (ℤ →+* α) where
  allEq := by
    suffices ∀f: ℤ →+* α, f = RingHom.intCast by
      intro a b; rw [this a, this b]
    intro f; ext z
    show f (Int.cast z) = _
    rw [RingHom.apply_intCast, map_intCast]

public theorem intCast_pown (n: ℤ) (m: ℕ) : (n ^ m: ℤ) = (n: α) ^ m :=
  map_pown (f := RingHom.intCast) _ _
