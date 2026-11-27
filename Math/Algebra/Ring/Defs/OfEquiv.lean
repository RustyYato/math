module

public import Math.Algebra.Semiring.Defs.OfEquiv
public import Math.Algebra.AddGroupWithOne.Defs.OfEquiv
public import Math.Algebra.Ring.Defs.Basic

namespace Math.OfEquiv

variable (f: α ≃ β)

public instance [Mul α] [Add α] [IsLeftDistrib α] : IsLeftDistrib (OfEquiv f) where
  mul_add a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    simp; rw [mul_add]
public instance [Mul α] [Add α] [IsRightDistrib α] : IsRightDistrib (OfEquiv f) where
  add_mul a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    simp; rw [add_mul]

public instance [AddGroupOps α] [Mul α] [IsNonUnitalNonAssocRing α] : IsNonUnitalNonAssocRing (OfEquiv f) where
public instance [AddGroupOps α] [Mul α] [IsNonUnitalRing α] : IsNonUnitalRing (OfEquiv f) where
public instance [AddGroupOps α] [One α] [Mul α] [NatCast α] [IntCast α] [IsNonAssocRing α] : IsNonAssocRing (OfEquiv f) where
public instance [RingOps α] [IsRing α] : IsRing (OfEquiv f) where
