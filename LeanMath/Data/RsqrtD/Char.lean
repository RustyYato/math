import LeanMath.Data.RsqrtD.Defs
import LeanMath.Algebra.Monoid.Char

 instance [AddMonoidOps α] [IsAddMonoid α] [HasChar α n] : HasChar (RsqrtD α d) n where
  dvd_iff_nsmul_eq_zero := by
    intro k
    apply Iff.intro
    · intro dvd a
      ext <;> apply (HasChar.dvd_iff_nsmul_eq_zero _).mp; assumption
      assumption
    · intro h
      apply (HasChar.dvd_iff_nsmul_eq_zero (α := α) _).mpr
      intro a
      have := h {
        real := a
        imag := 0
      }
      exact (RsqrtD.mk.inj this).left
