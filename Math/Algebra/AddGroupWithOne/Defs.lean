module

public import Math.Algebra.AddMonoidWithOne.Defs
public import Math.Algebra.Group.Defs

namespace Math

section Property

public class IsLawfulIntCast (α: Type*) [Neg α] [NatCast α] [IntCast α] where
  intCast_ofNat (n: ℕ) : (n: ℤ) = (n: α)
  intCast_negSucc (n: ℕ) : (Int.negSucc n: α) = -(n + 1: ℕ)

export IsLawfulIntCast (intCast_ofNat intCast_negSucc)

public class IsAddGroupWithOne (α: Type*) [AddGroupOps α] [One α] [NatCast α] [IntCast α] extends IsAddMonoidWithOne α, IsAddGroup α, IsLawfulIntCast α where

end Property

section Basic

public instance : IsAddGroupWithOne ℤ where
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

end Basic

section Theorems

public theorem map_intCast
  [Funlike F α β]
  [Add α] [Neg α] [Zero α] [One α] [NatCast α] [IntCast α]
  [AddGroupOps β] [One β] [NatCast β] [IntCast β]
  [IsLawfulNatCast α] [IsLawfulNatCast β] [IsLawfulNegLeft α]
  [IsLawfulIntCast α] [IsLawfulIntCast β] [IsAddGroup β]
  [IsAddHom F α β] [IsZeroHom F α β] [IsOneHom F α β]
  (f: F) (n: ℤ) : f n = n := by
  cases n with
  | ofNat n => dsimp; rw [intCast_ofNat, intCast_ofNat, map_natCast]
  | negSucc n => rw [intCast_negSucc, intCast_negSucc, map_neg, map_natCast]

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

public theorem zatCast_add (n m: ℤ) : (n + m: ℤ) = (n + m: α) := by
  rw [←zsmul_one_eq_intCast, add_zsmul, zsmul_one_eq_intCast, zsmul_one_eq_intCast]

end Theorems

namespace OfEquiv

variable (f: α ≃ β)

public instance [Neg α] [NatCast α] [IntCast α ] [IsLawfulIntCast α] : IsLawfulIntCast (OfEquiv f) where
  intCast_ofNat n := by simp; rw [intCast_ofNat]
  intCast_negSucc n := by simp; rw [intCast_negSucc]
public instance [AddGroupOps α] [One α] [NatCast α] [IntCast α] [IsAddGroupWithOne α] : IsAddGroupWithOne (OfEquiv f) where

end OfEquiv
