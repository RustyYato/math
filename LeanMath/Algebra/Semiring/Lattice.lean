import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Semiring.Set

open LatticeBuilder

namespace Subsemiring

variable [SemiringOps α] [IsSemiring α]

local instance : LatticeBuilder (Subsemiring α) where
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_one := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_one u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_mul u
  }

instance : LatticeBuilder.CompleteLattice (Subsemiring α) :=
  inferInstance

instance : IsCompleteLattice (Subsemiring α) := inferInstance

end Subsemiring
