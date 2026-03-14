import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Semiring.Ideal.TwoSided.Defs

namespace Ideal

variable [SemiringOps α] [IsSemiring α]

local instance : LatticeBuilder (Ideal α) where
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_left_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_left_mul u
    mem_right_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_right_mul u
  }

open LatticeBuilder
instance : LatticeBuilder.CompleteLattice (Ideal α) :=
  inferInstance

instance : IsCompleteLattice (Ideal α) := inferInstance

end Ideal
