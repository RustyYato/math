import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Group.Set

open LatticeBuilder

namespace Subgroup

variable [Mul α] [One α] [Inv α] [IsLawfulOneInv α] [IsLawfulOneMul α]

local instance : LatticeBuilder (Subgroup α) where
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
  }

instance : LatticeBuilder.BundledCompleteLattice (Subgroup α) :=
  inferInstance

instance : IsCompleteLattice (Subgroup α) := inferInstance

end Subgroup

namespace AddSubgroup

variable [Add α] [Zero α] [Neg α] [IsLawfulNegZero α] [IsLawfulZeroAdd α]

local instance : LatticeBuilder (AddSubgroup α) where
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
  }

instance : LatticeBuilder.BundledCompleteLattice (AddSubgroup α) :=
  inferInstance

instance : IsCompleteLattice (AddSubgroup α) := inferInstance

end AddSubgroup
