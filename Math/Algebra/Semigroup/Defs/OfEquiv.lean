module

public import Math.Data.OfEquiv.Defs
public import Math.Algebra.Semigroup.Defs.Basic

namespace Math.OfEquiv

variable (f: α ≃ β)

public instance [Mul α] [IsSemigroup α] : IsSemigroup (OfEquiv f) where
  mul_assoc a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    simp; rw [mul_assoc]
public instance [Add α] [IsAddSemigroup α] : IsAddSemigroup (OfEquiv f) where
  add_assoc a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    simp; rw [add_assoc]

public instance [Mul α] [IsComm α] : IsComm (OfEquiv f) where
  mul_comm a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    simp; rw [mul_comm]
public instance [Add α] [IsAddComm α] : IsAddComm (OfEquiv f) where
  add_comm a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    simp; rw [add_comm]

public instance [Mul α] [IsLeftCancel α] : IsLeftCancel (OfEquiv f) where
  of_mul_left {k a b} h := by
    induction k with | _ k =>
    induction a with | _ a =>
    induction b with | _ b =>
    simp at h
    rw [of_mul_left (OfEquiv.mk.inj h)]
public instance [Mul α] [IsRightCancel α] : IsRightCancel (OfEquiv f) where
  of_mul_right {k a b} h := by
    induction k with | _ k =>
    induction a with | _ a =>
    induction b with | _ b =>
    simp at h
    rw [of_mul_right (OfEquiv.mk.inj h)]
public instance [Mul α] [Zero α] [IsLeftCancel₀ α] : IsLeftCancel₀ (OfEquiv f) where
  of_mul_left₀ {k a b} hk h := by
    induction k with | _ k =>
    induction a with | _ a =>
    induction b with | _ b =>
    simp at h hk
    rw [of_mul_left₀ _ (OfEquiv.mk.inj h)]
    intro rfl; contradiction
public instance [Mul α] [Zero α] [IsRightCancel₀ α] : IsRightCancel₀ (OfEquiv f) where
  of_mul_right₀ {k a b} hk h := by
    induction k with | _ k =>
    induction a with | _ a =>
    induction b with | _ b =>
    simp at h hk
    rw [of_mul_right₀ _ (OfEquiv.mk.inj h)]
    intro rfl; contradiction
public instance [Add α] [IsLeftAddCancel α] : IsLeftAddCancel (OfEquiv f) where
  of_add_left {k a b} h := by
    induction k with | _ k =>
    induction a with | _ a =>
    induction b with | _ b =>
    simp at h
    rw [of_add_left (OfEquiv.mk.inj h)]
public instance [Add α] [IsRightAddCancel α] : IsRightAddCancel (OfEquiv f) where
  of_add_right {k a b} h := by
    induction k with | _ k =>
    induction a with | _ a =>
    induction b with | _ b =>
    simp at h
    rw [of_add_right (OfEquiv.mk.inj h)]
