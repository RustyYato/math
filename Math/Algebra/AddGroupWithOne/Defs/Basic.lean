module

public import Math.Algebra.AddMonoidWithOne.Defs.Basic
public import Math.Algebra.Group.Defs.Basic

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
