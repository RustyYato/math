import LeanMath.Algebra.Archimedean.Semifield
import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Ring.Order

def archimedean_iff_int_le [LE α] [LT α] [FieldOps α] [IsZeroLEOne α]
  [IsDivisionRing α] [IsOrderedSemiring α] : IsArchimedean α ↔ ∀ x : α, ∃ n : ℤ, x ≤ n := by
  apply Iff.trans archimedean_iff_nat_le
  apply Iff.intro
  · intro h x
    have ⟨n, hn⟩ := h x
    exists n; rwa [intCast_ofNat]
  · intro h x
    have ⟨n, hn⟩ := h x
    exists n.toNat
    apply le_trans hn
    rw [←intCast_ofNat]
    apply (intCast_le_intCast _ _).mpr
    exact Int.self_le_toNat n

def archimedean_iff_int_lt [LE α] [LT α] [FieldOps α] [IsZeroLEOne α]
  [IsDivisionRing α] [IsOrderedSemiring α] : IsArchimedean α ↔ ∀ x : α, ∃ n : ℤ, x < n := by
  apply Iff.trans archimedean_iff_nat_lt
  apply Iff.intro
  · intro h x
    have ⟨n, hn⟩ := h x
    exists n; rwa [intCast_ofNat]
  · intro h x
    have ⟨n, hn⟩ := h x
    exists n.toNat
    apply lt_of_lt_of_le hn
    rw [←intCast_ofNat]
    apply (intCast_le_intCast _ _).mpr
    exact Int.self_le_toNat n
