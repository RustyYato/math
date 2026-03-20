import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.Nat.Find

class HasChar (α: Type*) [AddMonoidOps α] [IsAddMonoid α] (c: outParam ℕ) where
  dvd_iff_nsmul_eq_zero (n: ℕ) : c ∣ n ↔ ∀a: α, n • a = 0

namespace HasChar

variable [AddMonoidOps α] [IsAddMonoid α] [AddMonoidOps β] [IsAddMonoid β]

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

def char_exists [LEM] (α: Type*) [AddMonoidOps α] [IsAddMonoid α] : ∃n, HasChar α n := by
  rcases em (∃n > 0, ∀a: α, n • a = 0) with h | h
  · have ⟨min, ⟨char_pos, char_spec⟩, lt_char⟩ := Relation.exists_min (α := ℕ) (· < ·) h
    exists min
    refine { dvd_iff_nsmul_eq_zero := fun n => ?_ }
    apply Iff.intro
    · rintro ⟨k, rfl⟩ _
      rw [mul_nsmul, char_spec, nsmul_zero]
    · intro g
      conv at g => {
        intro a
        rw [←Nat.div_add_mod n min,
          add_nsmul, mul_nsmul, char_spec, nsmul_zero, zero_add]
      }
      rw [Nat.dvd_iff_mod_eq_zero]
      apply Decidable.byContradiction
      intro nezero
      apply lt_char
      apply Nat.mod_lt n _
      assumption
      apply And.intro
      apply Nat.pos_of_ne_zero
      assumption
      assumption
  · exists 0
    simp only [gt_iff_lt, not_exists, not_and, LEM.not_forall] at h
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

open Classical in
noncomputable def char (α: Type*) [AddMonoidOps α] [IsAddMonoid α]: ℕ := Classical.choose (char_exists α)
open Classical in
def char_spec (α: Type*) [AddMonoidOps α] [IsAddMonoid α]: HasChar α (char α) := Classical.choose_spec (char_exists α)

def of_eqv [HasChar α n] (eqv: α ≃+ β) : HasChar β n where
  dvd_iff_nsmul_eq_zero x := by
    apply Iff.intro
    intro h a
    apply inj eqv.symm
    rw [map_nsmul, nsmul_eq_zero, map_zero]
    assumption
    intro h
    apply char_dvd (α := α)
    intro a
    apply inj eqv
    rw [map_nsmul, map_zero]
    apply h

def char_one_iff_subsingleton : HasChar α 1 ↔ Subsingleton α where
  mp h := by
    suffices ∀x: α, x = 0 by
      apply Subsingleton.intro
      intro a b; rw [this a, this b]
    intro a
    rw [←one_nsmul a, spec]
  mpr _ := {
    dvd_iff_nsmul_eq_zero n := by
      simp; intro; apply Subsingleton.allEq
  }

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
