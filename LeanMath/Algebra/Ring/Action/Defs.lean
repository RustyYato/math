import LeanMath.Algebra.Semiring.Action.Defs
import LeanMath.Algebra.Group.Action.Defs
import LeanMath.Algebra.Ring.Defs

variable [AddGroupOps α] [IsAddGroup α]

instance [IsAddComm α] : IsModule ℤ α where

variable [RingOps R] [IsRing R] [SMul R α]

def neg_smul_left [IsLeftDistribSMul R α] [IsLawfulZeroSMul R α] (r: R) (a: α) : -(r • a) = (-r) • a := by
  symm; apply eq_neg_of_add
  rw [←add_smul, neg_add_cancel, zero_smul]

def neg_smul_right [IsRightDistribSMul R α] [IsLawfulSMulZero R α] (r: R) (a: α) : -(r • a) = r • (-a) := by
  symm; apply eq_neg_of_add
  rw [←smul_add, neg_add_cancel, smul_zero]
