import LeanMath.Algebra.Archimedean.Defs
import LeanMath.Algebra.Semifield.Order

def archimedean_iff_nat_le [LE α] [LT α] [SemifieldOps α] [IsZeroLEOne α]
  [IsDivisionSemiring α] [IsOrderedSemiring α] [IsOrderedCancelAddCommMonoid α] : IsArchimedean α ↔ ∀ x : α, ∃ n : ℕ, x ≤ n := by
  apply Iff.intro
  · intro h x
    have ⟨n, hn⟩ := archidedean x (y := 1) (zero_lt_one α)
    rw [←natCast_eq_nsmul_one] at hn
    exists n
  · intro h
    refine ⟨?_⟩
    intro x y hy
    have ⟨n, hn⟩ := h (x /? y)
    exists n
    rw [nsmul_eq_natCast_mul]
    have := mul_le_mul_of_nonneg_right hn _ (le_of_lt hy)
    rwa [div?_mul_cancel] at this

def archimedean_iff_nat_lt [LE α] [LT α] [SemifieldOps α] [IsZeroLEOne α]
  [IsDivisionSemiring α] [IsOrderedSemiring α] [IsOrderedCancelAddCommMonoid α] : IsArchimedean α ↔ ∀ x : α, ∃ n : ℕ, x < n := by
  apply Iff.intro
  · intro h x
    have ⟨n, hn⟩ := archidedean x (y := 1) (zero_lt_one α)
    rw [←natCast_eq_nsmul_one] at hn
    exists n + 1
    apply lt_of_le_of_lt hn
    apply (natCast_lt_natCast _ _).mpr
    apply Nat.lt_succ_self
  · intro h
    refine ⟨?_⟩
    intro x y hy
    have ⟨n, hn⟩ := h (x /? y)
    exists n; apply le_of_lt
    rw [nsmul_eq_natCast_mul]
    have := mul_lt_mul_of_pos_right _ _ hn _ hy
    rwa [div?_mul_cancel] at this
