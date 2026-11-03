module

public import Math.Algebra.Module.Defs
public import Math.Algebra.Semiring.Congruence

namespace Math

variable (C R α: Type*)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α] [IsModule R α]
  [RelLike C α] [IsAddCon C α] [IsSMulCon C R α]
  (c: C)

instance : IsModule R (AlgQuot c) where
  smul_add r a b := by
    induction a using AlgQuot.ind with | _ a =>
    induction b using AlgQuot.ind with | _ b =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [smul_add]
  add_smul r s a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [add_smul]
  mul_smul r s a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [mul_smul]
  one_smul a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [one_smul]
  zero_smul a := by
    induction a using AlgQuot.ind with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [zero_smul]
  smul_zero r := by
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [smul_zero]
