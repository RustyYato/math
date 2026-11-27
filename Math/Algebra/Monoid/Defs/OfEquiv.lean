module

public import Math.Algebra.Semigroup.Defs.OfEquiv
public import Math.Algebra.Monoid.Defs.Basic

namespace Math.OfEquiv

variable (f: α ≃ β)

public instance [Mul α] [One α] [Pow α ℕ] [IsLawfulPowN α] : IsLawfulPowN (OfEquiv f) where
  pown_zero a := by
    induction a with | _ a =>
    simp; rw [pown_zero]
  pown_succ a n := by
    induction a with | _ a =>
    simp; rw [pown_succ]
public instance [Add α] [Zero α] [SMul ℕ α] [IsLawfulNSMul α] : IsLawfulNSMul (OfEquiv f) where
  zero_nsmul a := by
    induction a with | _ a =>
    simp; rw [zero_nsmul]
  succ_nsmul a n := by
    induction a with | _ a =>
    simp; rw [succ_nsmul]
public instance [Mul α] [One α] [IsLawfulOne α] : IsLawfulOne (OfEquiv f) where
  mul_one a := by
    induction a with | _ a =>
    simp; rw [mul_one]
  one_mul a := by
    induction a with | _ a =>
    simp; rw [one_mul]
public instance [Mul α] [Zero α] [IsLawfulZeroMul α] : IsLawfulZeroMul (OfEquiv f) where
  mul_zero a := by
    induction a with | _ a =>
    simp; rw [mul_zero]
  zero_mul a := by
    induction a with | _ a =>
    simp; rw [zero_mul]
public instance [Add α] [Zero α] [IsLawfulZero α] : IsLawfulZero (OfEquiv f) where
  add_zero a := by
    induction a with | _ a =>
    simp; rw [add_zero]
  zero_add a := by
    induction a with | _ a =>
    simp; rw [zero_add]
public instance [MonoidOps α] [IsMonoid α] : IsMonoid (OfEquiv f) where
public instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (OfEquiv f) where
