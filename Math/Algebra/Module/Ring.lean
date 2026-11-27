module

public import Math.Algebra.Module.Defs.Basic
public import Math.Algebra.Ring.Defs.Basic
public import Math.Algebra.Group.Action.Defs.Basic

namespace Math

variable [AddGroupOps α] [IsAddGroup α]

public instance [IsAddComm α] : IsModule ℤ α where


variable
  [SMul R α] [RingOps R] [IsRing R]
  [IsRightDistribSMul R α] [IsLeftDistribSMul R α]
  [IsLawfulMulSMul R α] [IsLawfulOneSMul R α]

public instance : IsLawfulZeroSMul R α where
  zero_smul a := by
    have : (0: R) • a + (0: R) • a = (0: R) • a := by rw [←add_smul, add_zero]
    replace := congrArg (f := fun x => x - (0: R) • a) this
    rwa [sub_self, add_sub_assoc, sub_self, add_zero] at this

public instance : IsLawfulSMulZero R α where
  smul_zero r := by
    have : r • (0: α) + r • (0: α) = r • (0: α) := by rw [←smul_add, add_zero]
    replace := congrArg (f := fun x => x - r • (0: α)) this
    rwa [sub_self, add_sub_assoc, sub_self, add_zero] at this
