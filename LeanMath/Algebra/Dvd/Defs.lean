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

instance [IsUnitsCentral α] [IsLeftCancel α] [IsRightCancel α] : IsDvdAntisymm α where
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

instance [ExcludedMiddleEq α] [Zero α] [IsLawfulZeroMul α] [IsUnitsCentral α] [IsLeftCancel₀ α] [IsRightCancel₀ α] : IsDvdAntisymm α where
  dvd_antisymm :=  by
    intro a b h₀ h₁
    obtain ⟨k₀, rfl⟩ := dvd_iff.mp h₀; clear h₀
    obtain ⟨k₁, h⟩ := dvd_iff.mp h₁; clear h₁
    rw [mul_assoc] at h; rw (occs := [1]) [←mul_one a] at h
    rcases em (a = 0) with ha | ha
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
  ∀⦃x y: α⦄, a = x * y -> a ∣ x ∨ a ∣ y

structure IsPrime (a: α) [Mul α] [Dvd α] [One α] [Zero α] : Prop where
  irreducible: ∀⦃x y: α⦄, a ∣ x * y -> a ∣ x ∨ a ∣ y
  ne_zero: a ≠ 0
  not_unit: ¬IsUnit a

structure IsComposite [Mul α] [One α] (n: α) : Prop where
  exists_factors: ∃a b: α, ¬IsUnit a ∧ ¬IsUnit b ∧ a * b = n

def IsComposite.not_unit [MonoidOps α] [IsComm α] [IsMonoid α] {c: α} (hc: IsComposite c) : ¬IsUnit c := by
  intro h
  obtain ⟨a, b, ha, hb, rfl⟩ := hc.exists_factors; clear hc
  have ⟨u, g⟩ := h.exists_eq_unit; clear h
  have : a * (b * u.inv) = 1 := by rw [←mul_assoc, g, u.val_mul_inv]
  have : (b * u.inv) * a = 1 := by rw [mul_comm, this]
  apply ha
  exists {
    val := a
    inv := b * u.inv
    val_mul_inv := by assumption
    inv_mul_val := by assumption
  }

def IsPrime.not_composite [ExcludedMiddleEq α] [MonoidOps α] [Zero α] [IsMonoid α] [IsComm α] [Dvd α]
  [IsLawfulZeroMul α] [IsLeftCancel₀ α] [IsRightCancel₀ α] [IsLawfulDvd α]
  {n: α} (hp: IsPrime n) (hc: IsComposite n) : False := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hc
  rcases em (a = 0) with rfl | ha'
  rw [zero_mul] at hp
  exact hp.ne_zero rfl
  rcases em (b = 0) with rfl | hb'
  rw [mul_zero] at hp
  exact hp.ne_zero rfl
  rcases hp.irreducible (dvd_refl _) with h | h
  · have ⟨u, hu⟩ := dvd_antisymm h (dvd_mul_left _ _)
    rw (occs := [2]) [←mul_one a] at hu
    rw [mul_assoc] at hu
    replace hu := of_mul_left₀ ha' hu
    have : b = u.inv := by rw [←one_mul u.inv, ←hu, mul_assoc, u.val_mul_inv, mul_one]
    rw [this] at hb
    apply hb
    exists u⁻¹
  · have ⟨u, hu⟩ := dvd_antisymm h (dvd_mul_right _ _)
    rw (occs := [2]) [←mul_one b] at hu
    rw [mul_comm a, mul_assoc] at hu
    replace hu := of_mul_left₀ hb' hu
    have : a = u.inv := by rw [←one_mul u.inv, ←hu, mul_assoc, u.val_mul_inv, mul_one]
    rw [this] at ha
    apply ha
    exists u⁻¹
