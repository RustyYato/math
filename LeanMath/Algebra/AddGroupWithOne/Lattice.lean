import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.AddGroupWithOne.Set

open LatticeBuilder

namespace AddSubgroupWithOne

variable [AddGroupWithOneOps α] [IsAddGroupWithOne α]

local instance : LatticeBuilder (AddSubgroupWithOne α) where
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
  }

instance : LatticeBuilder.BundledCompleteLattice (AddSubgroupWithOne α) :=
  inferInstance

instance : IsCompleteLattice (AddSubgroupWithOne α) := inferInstance

end AddSubgroupWithOne
