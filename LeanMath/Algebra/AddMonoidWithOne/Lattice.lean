import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.AddMonoidWithOne.Set

open LatticeBuilder

namespace AddSubMonoidWithOne

variable [AddMonoidWithOneOps α] [IsAddMonoidWithOne α]

local instance : LatticeBuilder (AddSubMonoidWithOne α) where
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
  }

instance : LatticeBuilder.CompleteLattice (AddSubMonoidWithOne α) :=
  inferInstance

instance : IsCompleteLattice (AddSubMonoidWithOne α) := inferInstance

end AddSubMonoidWithOne
