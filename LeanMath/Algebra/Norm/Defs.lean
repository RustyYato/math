import LeanMath.Tactic.TypeStar

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

class IsLawfulSemiNorm (α γ: Type*) [Norm α γ] [Norm γ γ] [SMul γ α] [Add α] [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulSemiAbs γ] where
  protected norm_nonneg (a: α): (0: γ) ≤ ‖a‖
  protected norm_smul (a: γ) (b: α) : ‖a • b‖ = ‖a‖ * ‖b‖
  protected norm_add_le_add_norm (a b: α) : ‖a + b‖ ≤ ‖a‖ + ‖b‖

class IsLawfulNorm (α γ: Type*) [Norm α γ] [Norm γ γ] [SMul γ α] [Add α] [Zero α] [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulAbs γ] extends IsLawfulSemiNorm α γ where
  protected norm_eq_zero {a: α} : ‖a‖ = 0 ↔ a = 0

class IsLawfulMulNorm (α γ: Type*) [Norm α γ] [Norm γ γ] [SMul γ α] [Add α] [Mul α] [LE γ] [Mul γ] [Add γ] [Zero γ] [IsLawfulSemiAbs γ] extends IsLawfulSemiNorm α γ where
  protected norm_mul (a b: α) : ‖a * b‖ = ‖a‖ * ‖b‖

instance [Norm α α] [Mul α] [Add α] [Zero α] [LE α] [IsLawfulSemiAbs α] :
  IsLawfulMulNorm α α where
  norm_nonneg := IsLawfulSemiAbs.abs_nonneg
  norm_smul := IsLawfulSemiAbs.abs_mul
  norm_add_le_add_norm := IsLawfulSemiAbs.abs_add_le_add_abs
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

variable [Norm α γ] [Norm γ γ] [SMul γ α] [Add α] [LE γ] [Mul γ] [Add γ] [Zero γ] [One γ]

-- def abs_one [IsLawfulSemiAbs γ] : ‖(1: γ)‖ = 1 := IsLawfulSemiAbs.abs_one
def norm_mul [Mul α] [IsLawfulSemiAbs γ] [IsLawfulMulNorm α γ] (a b: α) : ‖a * b‖ = ‖a‖ * ‖b‖ := IsLawfulMulNorm.norm_mul _ _

def norm_nonneg [IsLawfulSemiAbs γ] [IsLawfulSemiNorm α γ] (a: α): (0: γ) ≤ ‖a‖ := IsLawfulSemiNorm.norm_nonneg _
def norm_smul [IsLawfulSemiAbs γ] [IsLawfulSemiNorm α γ] (a: γ) (b: α) : ‖a • b‖ = ‖a‖ * ‖b‖ := IsLawfulSemiNorm.norm_smul _ _
def norm_add_le_add_norm [IsLawfulSemiAbs γ] [IsLawfulSemiNorm α γ] (a b: α) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := IsLawfulSemiNorm.norm_add_le_add_norm _ _
def norm_eq_zero [Zero α] [IsLawfulAbs γ] [IsLawfulNorm α γ] {a: α} : ‖a‖ = 0 ↔ a = 0 := IsLawfulNorm.norm_eq_zero
def of_norm_eq_zero [Zero α] [IsLawfulAbs γ] [IsLawfulNorm α γ] {a: α} : ‖a‖ = 0 -> a = 0 := IsLawfulNorm.norm_eq_zero.mp
@[simp] def norm_zero [Zero α] [IsLawfulAbs γ] [IsLawfulNorm α γ] : ‖(0: α)‖ = 0 := norm_eq_zero.mpr rfl

def abs_eq_of_nonneg [IsAbsMax γ] (a: γ): 0 ≤ a -> ‖a‖ = a := IsAbsMax.abs_eq_of_nonneg _

end
