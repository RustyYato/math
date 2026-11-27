module

public import Math.Algebra.Group.Defs.Lemmas
public import Math.Algebra.AddMonoidWithOne.Defs.Lemmas
public import Math.Algebra.AddGroupWithOne.Defs.Basic

namespace Math

public theorem intCast_zero
  [Add α] [Neg α] [Zero α] [One α] [NatCast α] [IntCast α]
  [IsLawfulNatCast α] [IsLawfulIntCast α] : (0: ℤ) = (0: α) := by
  show (Int.cast <| Nat.cast 0) = 0
  rw [intCast_ofNat, natCast_zero]

public theorem intCast_one
  [Add α] [Neg α] [Zero α] [One α] [NatCast α] [IntCast α]
  [IsLawfulNatCast α] [IsLawfulIntCast α] [IsLawfulZero α]
  : (1: ℤ) = (1: α) := by
  show (Int.cast <| Nat.cast 1) = 1
  rw [intCast_ofNat, natCast_one]

variable [AddGroupOps α] [One α]
  [NatCast α] [IntCast α] [IsAddGroupWithOne α]

public theorem zsmul_one_eq_intCast (n: ℤ) : n • (1: α) = n := by
  cases n with
  | ofNat n => dsimp; rw [ofNat_zsmul, intCast_ofNat, nsmul_one_eq_natCast]
  | negSucc n => rw [negSucc_zsmul, intCast_negSucc, nsmul_one_eq_natCast]

public theorem intCast_add (n m: ℤ) : (n + m: ℤ) = (n + m: α) := by
  rw [←zsmul_one_eq_intCast, add_zsmul, zsmul_one_eq_intCast, zsmul_one_eq_intCast]

public theorem intCast_neg (n: ℤ) : (-n: ℤ) = (-n: α) := by
  apply eq_neg_of_add
  rw [←intCast_add, neg_add_cancel, intCast_zero]
