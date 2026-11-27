module

public import Math.Algebra.Group.Defs.OfEquiv
public import Math.Algebra.AddMonoidWithOne.Defs.OfEquiv
public import Math.Algebra.AddGroupWithOne.Defs.Basic

namespace Math.OfEquiv

variable (f: α ≃ β)

public instance [Neg α] [NatCast α] [IntCast α ] [IsLawfulIntCast α] : IsLawfulIntCast (OfEquiv f) where
  intCast_ofNat n := by simp; rw [intCast_ofNat]
  intCast_negSucc n := by simp; rw [intCast_negSucc]
public instance [AddGroupOps α] [One α] [NatCast α] [IntCast α] [IsAddGroupWithOne α] : IsAddGroupWithOne (OfEquiv f) where
