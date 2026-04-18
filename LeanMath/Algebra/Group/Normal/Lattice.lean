import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Group.Normal.Defs

open LatticeBuilder

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α]

local instance : LatticeBuilder (NormalSubgroup α) where
  create u hu := {
    toSet := u
    mem_one := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_one u
    mem_inv := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_inv u
    mem_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_mul u
    mem_conj := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_conj u
  }

instance : LatticeBuilder.BundledCompleteLattice (NormalSubgroup α) :=
  inferInstance

instance : IsCompleteLattice (NormalSubgroup α) := inferInstance

end NormalSubgroup

namespace NormalAddSubgroup

variable [AddGroupOps α] [IsAddGroup α]

local instance : LatticeBuilder (NormalAddSubgroup α) where
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_neg := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_neg u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_add_conj := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add_conj u
  }

instance : LatticeBuilder.BundledCompleteLattice (NormalAddSubgroup α) :=
  inferInstance

instance : IsCompleteLattice (NormalAddSubgroup α) := inferInstance

end NormalAddSubgroup
