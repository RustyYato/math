import LeanMath.Algebra.Monoid.Defs

class IsLawfulDvd (α: Type*) [Dvd α] [Mul α]: Prop where
  protected dvd_iff {a b: α} : (a ∣ b) ↔ ∃k, b = a * k := by intros; rfl

def dvd_iff [Dvd α] [Mul α] [IsLawfulDvd α] {a b: α} : (a ∣ b) ↔ ∃k, b = a * k :=
  IsLawfulDvd.dvd_iff

namespace IsLawfulDvd.ofMul

variable [Mul α]

scoped instance : Dvd α where
  dvd a b := ∃k, b = a * k

scoped instance : IsLawfulDvd α where

end IsLawfulDvd.ofMul

instance : IsLawfulDvd Nat where
instance : IsLawfulDvd Int where

section

variable [MonoidOps α] [IsMonoid α] [Dvd α] [IsLawfulDvd α]

def unit_dvd (a b: α) [IsUnit a] : a ∣ b := by
  obtain ⟨u, rfl⟩ := IsUnit.exists_eq_unit (a := a)
  apply dvd_iff.mpr
  exists u.inv * b
  rw [←mul_assoc, u.val_mul_inv, one_mul]

class IsDvdAntisymm (α: Type*) [MonoidOps α] [IsMonoid α] [IsUnitsCentral α] [Dvd α] where
  dvd_antisymm {a b: α} (h₀: a ∣ b) (h₁: b ∣ a) : Units.Associates a b

instance [DecidableEq α] [IsUnitsCentral α] [IsLeftCancel α] [IsRightCancel α] : IsDvdAntisymm α where
  dvd_antisymm :=  by
    intro a b h₀ h₁
    obtain ⟨k₀, rfl⟩ := dvd_iff.mp h₀; clear h₀
    obtain ⟨k₁, h⟩ := dvd_iff.mp h₁; clear h₁
    rw [mul_assoc] at h; rw (occs := [1]) [←mul_one a] at h
    replace h := of_mul_left h.symm
    exists {
      val := k₀
      inv := k₁
      val_mul_inv := h
      inv_mul_val := by
        apply of_mul_right (k := k₁)
        rw [mul_assoc, h, one_mul, mul_one]
    }

instance [DecidableEq α] [Zero α] [IsLawfulZeroMul α] [IsUnitsCentral α] [IsLeftCancel₀ α] [IsRightCancel₀ α] : IsDvdAntisymm α where
  dvd_antisymm :=  by
    intro a b h₀ h₁
    obtain ⟨k₀, rfl⟩ := dvd_iff.mp h₀; clear h₀
    obtain ⟨k₁, h⟩ := dvd_iff.mp h₁; clear h₁
    rw [mul_assoc] at h; rw (occs := [1]) [←mul_one a] at h
    by_cases ha:a = 0
    subst a; exists 1
    rw [zero_mul, zero_mul]
    replace h := of_mul_left₀ ha h.symm
    exists {
      val := k₀
      inv := k₁
      val_mul_inv := h
      inv_mul_val := by
        apply of_mul_right₀ (k := k₁)
        rintro rfl; rw [mul_zero] at h
        have : a * 1 ≠ 0 := by rwa [mul_one]
        rw [←h, mul_zero] at this
        contradiction
        rw [mul_assoc, h, one_mul, mul_one]
    }

def dvd_antisymm [MonoidOps α] [IsMonoid α] [IsUnitsCentral α] [Dvd α] [IsDvdAntisymm α] {a b: α} (h₀: a ∣ b) (h₁: b ∣ a) : Units.Associates a b :=
  IsDvdAntisymm.dvd_antisymm h₀ h₁

instance : IsDvdAntisymm ℕ := inferInstance
instance : IsDvdAntisymm ℤ := inferInstance

end

section

variable [Mul α] [Dvd α] [IsLawfulDvd α]

def dvd_mul_left (a b: α) : a ∣ a * b := by
  apply dvd_iff.mpr
  exists b
def dvd_mul_right [IsComm α] (a b: α) : a ∣ b * a := by
  rw [mul_comm]; apply dvd_mul_left

def dvd_trans [IsSemigroup α] {a b c: α} : a ∣ b -> b ∣ c -> a ∣ c := by
  intro h g
  obtain ⟨k₀, rfl⟩ := dvd_iff.mp h
  obtain ⟨k₁, rfl⟩ := dvd_iff.mp g
  rw [mul_assoc]
  apply dvd_mul_left

def dvd_refl [One α] [IsLawfulOneMul α] (a: α) : a ∣ a := by
  apply dvd_iff.mpr
  exists 1; rw [mul_one]

instance [One α] [IsLawfulOneMul α] : Relation.IsRefl (α := α) (· ∣ ·) where
  refl := dvd_refl
instance [IsSemigroup α] : Relation.IsTrans (α := α) (· ∣ ·) where
  trans := dvd_trans

end

def IsIrreducible (a: α) [Mul α] [Dvd α] : Prop :=
  ∀x y: α, a = x * y -> a ∣ x ∨ a ∣ y

structure IsPrime (a: α) [Mul α] [Dvd α] [One α] [Zero α] : Prop where
  irreducible: IsIrreducible a
  ne_zero: a ≠ 0
  not_unit: ¬IsUnit a
