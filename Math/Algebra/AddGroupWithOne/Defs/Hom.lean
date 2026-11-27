module

public import Math.Algebra.Group.Defs.Hom
public import Math.Algebra.AddMonoidWithOne.Defs.Hom
public import Math.Algebra.AddGroupWithOne.Defs.Basic

namespace Math

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
