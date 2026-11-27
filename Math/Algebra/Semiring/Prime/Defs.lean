module

public import Math.Algebra.Semiring.Defs.Basic
public import Math.Algebra.Monoid.Units

namespace Math

public class IsLawfulDvd (α: Type*) [Dvd α] [Mul α] where
  dvd_iff {a b: α} : (a ∣ b) ↔ ∃k, b = a * k := by intros; rfl

public class IsNotUnit [Mul α] [One α] (p: α) : Prop where
  not_unit: ¬IsUnit p

public class IsPrime [Dvd α] [Mul α] [One α] (p: α) : Prop extends IsNotUnit p where
  dvd_of_dvd_mul: ∀a b: α, p ∣ a * b -> p ∣ a ∨ p ∣ b

public class IsIrreducible [Mul α] [One α] (p: α) : Prop extends IsNotUnit p where
  unit_of_eq_mul: ∀a b: α, p = a * b -> IsUnit a ∨ IsUnit b

public class IsComposite [Mul α] [One α] (x: α) : Prop extends IsNotUnit x where
  exists_eq_prod : ∃a b: α, IsNotUnit a ∧ IsNotUnit b ∧ x = a * b

export IsNotUnit (not_unit)
export IsLawfulDvd (dvd_iff)
export IsPrime (dvd_of_dvd_mul)
export IsIrreducible (unit_of_eq_mul)
export IsComposite (exists_eq_prod)

public instance : IsLawfulDvd ℕ where
public instance : IsLawfulDvd ℤ where

public instance [Zero α] [One α] [IsZeroNeOne α] [Mul α] [IsLawfulZeroMul α] : IsNotUnit (α := α) 0 where
  not_unit := by
    intro ⟨u, h⟩
    have := u.inv_mul_val
    rw [h, mul_zero] at this
    exact zero_ne_one this
public instance [Zero α] [One α] [IsZeroNeOne α] [NatCast α] [Add α] [IsLawfulNatCast α] [Mul α] [IsLawfulZeroMul α] : IsNotUnit (α := α) (0: ℕ) := by
    rw [natCast_zero]; infer_instance
public instance (n: ℕ) : IsNotUnit (n + 2) where
  not_unit := by
    intro ⟨u, hu⟩
    have := u.inv_mul_val
    rw [hu] at this
    nomatch Nat.eq_one_of_mul_eq_one_left this
public instance (n: ℕ) : IsNotUnit (Int.ofNat (n + 2): ℤ) where
  not_unit := by
    intro ⟨u, hu⟩
    have := u.inv_mul_val
    rw [hu] at this
    nomatch Int.eq_one_of_mul_eq_one_left (Int.natCast_nonneg _) this
public instance (n: ℕ) : IsNotUnit (Int.negSucc (n + 1)) where
  not_unit := by
    intro ⟨u, hu⟩
    have := u.inv_mul_val
    rw [hu, Int.negSucc_eq, Int.mul_neg, ←Int.neg_mul] at this
    nomatch Int.eq_one_of_mul_eq_one_left (Int.natCast_nonneg _) this
public instance (n: ℕ) : IsNotUnit ((n + 2: ℕ): ℤ) := inferInstanceAs (IsNotUnit (Int.ofNat (n + 2)))

variable [Dvd α] [Mul α] [IsLawfulDvd α]

public theorem unit_dvd [One α] [IsSemigroup α] [IsLawfulOne α] (a b: α) [h: IsUnit a] : a ∣ b := by
  apply dvd_iff.mpr
  obtain ⟨u, rfl⟩ := h
  exists u.inv * b
  rw [←mul_assoc, u.val_mul_inv, one_mul]

public theorem one_dvd [One α] [IsLawfulOne α] (a: α) : 1 ∣ a := by
  apply dvd_iff.mpr
  exists a; rw [one_mul]

public theorem dvd_mul_right (a b: α) : a ∣ a * b := by
  apply dvd_iff.mpr
  exists b
public theorem dvd_mul_left (a b: α) [IsCommAt a b] : a ∣ b * a := by
  apply dvd_iff.mpr
  exists b; rw [mul_comm]

public theorem dvd_refl [One α] [IsLawfulOne α] (a: α) : a ∣ a := by
  apply dvd_iff.mpr
  exists 1; rw [mul_one]

public theorem dvd_zero [Zero α] [IsLawfulZeroMul α] (a: α) : a ∣ 0 := by
  apply dvd_iff.mpr
  exists 0; rw [mul_zero]

public theorem dvd_trans [IsSemigroup α] {a b c: α} : a ∣ b -> b ∣ c -> a ∣ c := by
  intro h g
  apply dvd_iff.mpr
  replace h := dvd_iff.mp h
  replace g := dvd_iff.mp g
  obtain ⟨k₀, rfl⟩ := h
  obtain ⟨k₁, rfl⟩ := g
  exists k₀ * k₁
  rw [mul_assoc]
