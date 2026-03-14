import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.Nat.Find

class HasChar (α: Type*) [AddMonoidOps α] [IsAddMonoid α] (c: outParam ℕ) where
  dvd_iff_nsmul_eq_zero (n: ℕ) : c ∣ n ↔ ∀a: α, n • a = 0

namespace HasChar

variable [AddMonoidOps α] [IsAddMonoid α]

def char_dvd [HasChar α c] (n: ℕ) : (∀a: α, n • a = 0) -> c ∣ n :=
  (HasChar.dvd_iff_nsmul_eq_zero n).mpr

def nsmul_eq_zero [HasChar α c] (n: ℕ) (h: c ∣ n) : ∀a: α, n • a = 0 :=
  (HasChar.dvd_iff_nsmul_eq_zero _).mp h

def spec [HasChar α c] : ∀a: α, c • a = 0 :=
  nsmul_eq_zero _ (Nat.dvd_refl _)

def unique (h₀: HasChar α n) (h₁: HasChar α m) : n = m := by
  apply Nat.dvd_antisymm
  apply @char_dvd α _ _ _ h₀
  apply @spec _ _ _ _ h₁
  apply @char_dvd α _ _ _ h₁
  apply @spec _ _ _ _ h₀

def char_exists (α: Type*) [AddMonoidOps α] [IsAddMonoid α] : ∃n, HasChar α n := by
  classical
  by_cases h:∃n > 0, ∀a: α, n • a = 0
  · exists Nat.find h
    have ⟨char_pos, char_spec⟩ := Nat.find_spec h
    have lt_char := Nat.find_minimal h
    refine { dvd_iff_nsmul_eq_zero := fun n => ?_ }
    apply Iff.intro
    · rintro ⟨k, rfl⟩ _
      rw [mul_nsmul, char_spec, nsmul_zero]
    · intro g
      conv at g => {
        intro a
        rw [←Nat.div_add_mod n (Nat.find h),
          add_nsmul, mul_nsmul, char_spec, nsmul_zero, zero_add]
      }
      rw [Nat.dvd_iff_mod_eq_zero]
      apply Decidable.byContradiction
      intro nezero
      apply lt_char
      apply Nat.mod_lt n _
      assumption
      apply And.intro
      omega
      assumption
  · exists 0
    simp at h
    refine { dvd_iff_nsmul_eq_zero := fun n => ?_ }
    apply Iff.intro
    · rintro ⟨_, rfl⟩
      simp [zero_nsmul]
    intro hk
    cases n with
    | zero => apply Nat.dvd_refl
    | succ n =>
      exfalso
      have ⟨a, ha⟩ := h (n + 1) (Nat.zero_lt_succ _)
      exact ha (hk _)

noncomputable def char (α: Type*) [AddMonoidOps α] [IsAddMonoid α]: ℕ := Classical.choose (char_exists α)
def char_spec (α: Type*) [AddMonoidOps α] [IsAddMonoid α]: HasChar α (char α) := Classical.choose_spec (char_exists α)

end HasChar

instance : HasChar ℕ 0 where
  dvd_iff_nsmul_eq_zero n := by
    apply Iff.intro
    rintro ⟨_, rfl⟩
    simp [zero_nsmul]
    intro h
    cases n
    apply Nat.dvd_refl
    have := h 1
    nomatch this

instance : HasChar ℤ 0 where
  dvd_iff_nsmul_eq_zero n := by
    apply Iff.intro
    rintro ⟨_, rfl⟩
    simp [zero_nsmul]
    intro h
    cases n
    apply Nat.dvd_refl
    have := h 1
    nomatch this
