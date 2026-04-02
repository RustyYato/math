import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Ring.Set

open LatticeBuilder

namespace Subring

variable [RingOps α] [IsRing α]

local instance : LatticeBuilder (Subring α) where
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_one := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_one u
    mem_neg := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_neg u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_mul u
  }

instance : LatticeBuilder.BundledCompleteLattice (Subring α) :=
  inferInstance

instance : IsCompleteLattice (Subring α) := inferInstance

end Subring
