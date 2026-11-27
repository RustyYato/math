module

public import Math.Algebra.Monoid.Defs.OfEquiv
public import Math.Algebra.AddMonoidWithOne.Defs.Basic

namespace Math.OfEquiv

variable (f: α ≃ β)

public instance [Add α] [Zero α] [One α] [NatCast α] [IsLawfulNatCast α] : IsLawfulNatCast (OfEquiv f) where
  natCast_zero := by simp; rw [natCast_zero]
  natCast_succ n := by simp; rw [natCast_succ]
public instance [AddMonoidOps α] [One α] [NatCast α] [IsAddMonoidWithOne α] : IsAddMonoidWithOne (OfEquiv f) where
