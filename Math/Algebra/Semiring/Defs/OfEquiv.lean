module

public import Math.Algebra.AddMonoidWithOne.Defs.OfEquiv
public import Math.Algebra.Semiring.Defs.Basic

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

public instance [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α] : IsNonUnitalNonAssocSemiring (OfEquiv f) where
public instance [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α] : IsNonUnitalSemiring (OfEquiv f) where
public instance [AddMonoidOps α] [One α] [Mul α] [NatCast α] [IsNonAssocSemiring α] : IsNonAssocSemiring (OfEquiv f) where
public instance [SemiringOps α] [IsSemiring α] : IsSemiring (OfEquiv f) where
