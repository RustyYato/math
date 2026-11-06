module

public import Math.Algebra.Monoid.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace Submonoid

variable [MonoidOps α] [IsMonoid α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (Submonoid α) α where
  create u hu := {
    toSet := u
    mem_one := MemOne.copy u hu
    mem_mul := MemMul.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (Submonoid α) := latticeBuilder.instCompleteLattice

end Submonoid

namespace AddSubmonoid

variable [AddMonoidOps α] [IsAddMonoid α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (AddSubmonoid α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_add := MemAdd.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (AddSubmonoid α) := latticeBuilder.instCompleteLattice

end AddSubmonoid
