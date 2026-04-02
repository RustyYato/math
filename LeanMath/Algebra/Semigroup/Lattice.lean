import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Semigroup.Set

open LatticeBuilder

namespace SubSemigroup

variable [Mul α]

local instance : LatticeBuilder (SubSemigroup α) where
  create u hu := {
    toSet := u
    mem_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_mul u
  }

instance : LatticeBuilder.BundledCompleteLattice (SubSemigroup α) :=
  inferInstance

instance : IsCompleteLattice (SubSemigroup α) := inferInstance

end SubSemigroup

namespace AddSubSemigroup

variable [Add α]

local instance : LatticeBuilder (AddSubSemigroup α) where
  create u hu := {
    toSet := u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
  }

instance : LatticeBuilder.BundledCompleteLattice (AddSubSemigroup α) :=
  inferInstance

instance : IsCompleteLattice (AddSubSemigroup α) := inferInstance

end AddSubSemigroup
