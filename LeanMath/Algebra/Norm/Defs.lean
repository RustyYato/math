import LeanMath.Tactic.TypeStar
import LeanMath.Data.OfEquiv.Defs

class Norm (α: Type*) (γ: outParam Type*) where
  protected norm : α -> γ

notation "‖" a "‖" => Norm.norm a

class IsLawfulSemiAbs (α: Type*) [Norm α α] [Mul α] [Add α] [Zero α] [LE α] where
  protected abs_nonneg (a: α): (0: α) ≤ ‖a‖
  protected abs_mul (a b: α) : ‖a * b‖ = ‖a‖ * ‖b‖
  protected abs_add_le_add_abs (a b: α) : ‖a + b‖ ≤ ‖a‖ + ‖b‖

class IsLawfulAbs (α: Type*) [Norm α α] [Mul α] [Add α] [Zero α] [LE α] extends IsLawfulSemiAbs α where
  protected abs_eq_zero {a: α} : ‖a‖ = 0 ↔ a = 0

class IsAbsMax (α: Type*) [Norm α α] [Zero α] [LE α] where
  protected abs_eq_of_nonneg (a: α): 0 ≤ a -> ‖a‖ = a

class IsNormNonneg (α γ: Type*) [Norm α γ] [Zero γ] [LE γ] where
  protected norm_nonneg (a: α): (0: γ) ≤ ‖a‖

class IsNormSMul (α γ: Type*) [Norm α γ] [Norm γ γ] [SMul γ α] [Mul γ] where
  protected norm_smul (a: γ) (b: α): ‖a • b‖ = ‖a‖ * ‖b‖

class IsNormSubAdd (α γ: Type*) [Norm α γ] [Norm γ γ] [Add α] [Add γ] [LE γ] where
  protected norm_add_le_add_norm (a b: α) : ‖a + b‖ ≤ ‖a‖ + ‖b‖

class IsNormSubMul (α γ: Type*) [Norm α γ] [Norm γ γ] [Mul α] [Mul γ] [LE γ] where
  protected norm_mul_le_mul_norm (a b: α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖

class IsNormMul (α γ: Type*) [Norm α γ] [Norm γ γ] [Mul α] [Mul γ] where
  protected norm_mul (a b: α) : ‖a * b‖ = ‖a‖ * ‖b‖

class IsNormPosDef (α γ: Type*) [Norm α γ] [Zero α] [Zero γ] [LE γ]  extends IsNormNonneg α γ where
  protected norm_eq_zero {a: α} : ‖a‖ = 0 ↔ a = 0

class IsLawfulSemiNorm (α γ: Type*)
  [Norm α γ] [Norm γ γ] [SMul γ α] [Add α]
  [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulSemiAbs γ]
  extends IsNormNonneg α γ, IsNormSMul α γ, IsNormSubAdd α γ where

class IsLawfulNorm (α γ: Type*)
  [Norm α γ] [Norm γ γ] [SMul γ α] [Zero α] [Add α]
  [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulAbs γ] extends IsLawfulSemiNorm α γ, IsNormPosDef α γ where

instance [Norm α α] [Mul α] [Add α] [Zero α] [LE α] [IsLawfulSemiAbs α] :
  IsLawfulSemiNorm α α where
  norm_nonneg := IsLawfulSemiAbs.abs_nonneg
  norm_smul := IsLawfulSemiAbs.abs_mul
  norm_add_le_add_norm := IsLawfulSemiAbs.abs_add_le_add_abs

instance [Norm α α] [Mul α] [Add α] [Zero α] [LE α] [IsLawfulSemiAbs α] :
  IsNormMul α α where
  norm_mul := IsLawfulSemiAbs.abs_mul

instance [Norm α α] [Mul α] [Add α] [Zero α] [LE α] [IsLawfulAbs α] :
  IsLawfulNorm α α where
  norm_eq_zero := IsLawfulAbs.abs_eq_zero

instance : Norm ℕ ℕ where
  norm := id
instance : Norm ℤ ℤ where
  norm x := x.natAbs

instance : IsLawfulAbs ℕ where
  abs_nonneg := Nat.zero_le
  abs_mul _ _ := rfl
  abs_add_le_add_abs _ _ := Nat.le_refl _
  abs_eq_zero := Iff.rfl

instance : IsLawfulAbs ℤ where
  abs_nonneg _ := Int.natCast_nonneg _
  abs_mul _ _ := by
    apply Eq.trans _ (Int.natCast_mul _ _)
    show (Int.natAbs _ :ℤ) = _
    congr
    rw [Int.natAbs_mul]
  abs_eq_zero {a} := {
    mp h := match a with | 0 => rfl
    mpr h := match a with | 0 => rfl
  }
  abs_add_le_add_abs a b := by
    apply Int.ofNat_le.mpr
    apply Int.natAbs_add_le

instance : IsAbsMax ℕ where
  abs_eq_of_nonneg _ _ := rfl
instance : IsAbsMax ℤ where
  abs_eq_of_nonneg
  | .ofNat _, _ => rfl

section

variable [Norm α γ] [Norm γ γ] [SMul γ α]
  [Zero α] [Add α]
  [LE γ] [Mul γ] [Add γ] [Zero γ]

def norm_mul_le_mul_norm [Mul α] [IsNormSubMul α γ] (a b: α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := IsNormSubMul.norm_mul_le_mul_norm _ _
def norm_mul [Mul α] [IsNormMul α γ] (a b: α) : ‖a * b‖ = ‖a‖ * ‖b‖ := IsNormMul.norm_mul _ _

def norm_nonneg [IsNormNonneg α γ] (a: α): (0: γ) ≤ ‖a‖ := IsNormNonneg.norm_nonneg _
def norm_smul [IsNormSMul α γ] (a: γ) (b: α) : ‖a • b‖ = ‖a‖ * ‖b‖ := IsNormSMul.norm_smul _ _
def norm_add_le_add_norm [IsNormSubAdd α γ] (a b: α) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := IsNormSubAdd.norm_add_le_add_norm _ _
def norm_eq_zero [IsNormPosDef α γ] {a: α} : ‖a‖ = 0 ↔ a = 0 := IsNormPosDef.norm_eq_zero
def of_norm_eq_zero [IsNormPosDef α γ] {a: α} : ‖a‖ = 0 -> a = 0 := norm_eq_zero.mp
@[simp] def norm_zero [IsNormPosDef α γ] : ‖(0: α)‖ = 0 := norm_eq_zero.mpr rfl

def abs_eq_of_nonneg [IsAbsMax γ] (a: γ): 0 ≤ a -> ‖a‖ = a := IsAbsMax.abs_eq_of_nonneg _

end

namespace OfEquiv

variable {α β γ: Type*} (f: α ≃ β)

namespace NormExt

protected scoped instance [Norm β γ] : Norm (OfEquiv f) γ where
  norm a := ‖f a‖

@[simp] protected def norm_def [Norm β γ] (a: OfEquiv f) : ‖a‖ = ‖f a‖ := rfl

variable
  [Norm β γ] [Norm γ γ] [SMul γ β] [Zero β] [Add β] [Mul β] [LE γ] [Mul γ] [Add γ] [Zero γ]

protected scoped instance [IsNormNonneg β γ]
  : IsNormNonneg (OfEquiv f) γ where
  norm_nonneg a := by dsimp; apply norm_nonneg

protected scoped instance [IsNormPosDef β γ] : IsNormPosDef (OfEquiv f) γ where
  norm_eq_zero {a} := by
    dsimp; apply Iff.trans norm_eq_zero
    apply Iff.trans Equiv.symm_eq_iff.symm
    apply Eq.comm

protected scoped instance [IsNormSMul β γ] : IsNormSMul (OfEquiv f) γ where
  norm_smul a b := by simp; apply norm_smul

protected scoped instance [IsNormMul β γ] : IsNormMul (OfEquiv f) γ where
  norm_mul a b := by simp; apply norm_mul

protected scoped instance [IsNormSubAdd β γ] : IsNormSubAdd (OfEquiv f) γ where
  norm_add_le_add_norm a b := by simp; apply norm_add_le_add_norm

protected scoped instance [IsNormSubMul β γ] : IsNormSubMul (OfEquiv f) γ where
  norm_mul_le_mul_norm a b := by simp; apply norm_mul_le_mul_norm

protected scoped instance
  [Norm β γ] [Norm γ γ] [SMul γ β] [Add β] [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulSemiAbs γ]
  [IsLawfulSemiNorm β γ]
  : IsLawfulSemiNorm (OfEquiv f) γ where
  norm_nonneg a := by dsimp; apply norm_nonneg
  norm_smul a b  := by dsimp; rw [Equiv.symm_coe, norm_smul]
  norm_add_le_add_norm a b := by dsimp; rw [Equiv.symm_coe]; apply norm_add_le_add_norm

protected scoped instance
  [Norm β γ] [Norm γ γ] [SMul γ β] [Add β] [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulSemiAbs γ]
  [IsLawfulSemiNorm β γ]
  : IsLawfulSemiNorm (OfEquiv f) γ where
  norm_nonneg a := by dsimp; apply norm_nonneg
  norm_smul a b  := by dsimp; rw [Equiv.symm_coe, norm_smul]
  norm_add_le_add_norm a b := by dsimp; rw [Equiv.symm_coe]; apply norm_add_le_add_norm

protected scoped instance
  [Norm β γ] [Norm γ γ] [SMul γ β] [Zero β] [Add β] [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulAbs γ]
  [IsLawfulNorm β γ]
  : IsLawfulNorm (OfEquiv f) γ where
  norm_eq_zero {a} := by
    dsimp; apply Iff.trans norm_eq_zero
    refine Function.Injective.eq_iff' ?_ ?_
    exact inj f; rw [Equiv.symm_coe]

end NormExt

namespace NormSelf

protected scoped instance [Norm β β] : Norm (OfEquiv f) (OfEquiv f) where
  norm a := f.symm ‖f a‖

@[simp] protected def norm_def [Norm β β] (a: OfEquiv f) : ‖a‖ = f.symm ‖f a‖ := rfl

protected scoped instance
  [Norm β β] [Mul β] [Add β] [Zero β] [LE β] [IsLawfulSemiAbs β] :
  IsLawfulSemiAbs (OfEquiv f) where
  abs_nonneg a := by dsimp; rw [Equiv.symm_coe, Equiv.symm_coe]; apply norm_nonneg
  abs_mul a b  := by dsimp; rw [Equiv.symm_coe, Equiv.symm_coe, Equiv.symm_coe, norm_mul]
  abs_add_le_add_abs a b := by
    dsimp; repeat rw [Equiv.symm_coe]
    apply norm_add_le_add_norm
    repeat rw [Equiv.coe_symm]

protected scoped instance
  [Norm β β] [Mul β] [Add β] [Zero β] [LE β] [IsLawfulAbs β] :
  IsLawfulAbs (OfEquiv f) where
  abs_eq_zero {a} := by
    dsimp; apply Iff.trans (inj f.symm).eq_iff
    apply Iff.trans norm_eq_zero
    refine Function.Injective.eq_iff' ?_ ?_
    exact inj f; rw [Equiv.symm_coe]

protected scoped instance
  [Norm β β] [Zero β] [LE β] [IsAbsMax β] :
  IsAbsMax (OfEquiv f) where
  abs_eq_of_nonneg a := by
    dsimp; rw [Equiv.symm_coe]
    intro h; rwa [abs_eq_of_nonneg, Equiv.coe_symm]

end NormSelf

end OfEquiv
