module

public import Math.Algebra.Monoid.Action.Defs.Basic
public import Math.Algebra.Monoid.Defs.OfEquiv

namespace Math.OfEquiv

variable (f: α ≃ β)

public instance [SMul S α] [Zero α] [IsLawfulSMulZero S α] : IsLawfulSMulZero S (OfEquiv f) where
  smul_zero r := by simp; rw [smul_zero]
public instance [SMul S α] [Zero S] [Zero α] [IsLawfulZeroSMul S α] : IsLawfulZeroSMul S (OfEquiv f) where
  zero_smul a := by
    induction a
    simp; rw [zero_smul]
public instance [SMul S α] [Add α] [IsRightDistribSMul S α] : IsRightDistribSMul S (OfEquiv f) where
  smul_add r a b := by
    induction a; induction b
    simp; rw [smul_add]
public instance [SMul S α] [Add S] [Add α] [IsLeftDistribSMul S α] : IsLeftDistribSMul S (OfEquiv f) where
  add_smul r s a := by
    induction a
    simp; rw [add_smul]
public instance [SMul S α] [One S] [IsLawfulOneSMul S α] : IsLawfulOneSMul S (OfEquiv f) where
  one_smul a := by induction a; simp; rw [one_smul]
public instance [SMul S α] [Mul S] [IsLawfulMulSMul S α] : IsLawfulMulSMul S (OfEquiv f) where
  mul_smul r s a := by induction a; simp; rw [mul_smul]
