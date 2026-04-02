import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Monoid.Set

open LatticeBuilder

namespace SubMonoid

variable [Mul α] [One α] [IsLawfulOneMul α]

local instance : LatticeBuilder (SubMonoid α) where
  create u hu := {
    toSet := u
    mem_one := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_one u
    mem_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_mul u
  }

instance : LatticeBuilder.BundledCompleteLattice (SubMonoid α) :=
  inferInstance

instance : IsCompleteLattice (SubMonoid α) := inferInstance

end SubMonoid

namespace AddSubMonoid

variable [Add α] [Zero α] [IsLawfulZeroAdd α]

local instance : LatticeBuilder (AddSubMonoid α) where
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
  }

instance : LatticeBuilder.BundledCompleteLattice (AddSubMonoid α) :=
  inferInstance

instance : IsCompleteLattice (AddSubMonoid α) := inferInstance

end AddSubMonoid
