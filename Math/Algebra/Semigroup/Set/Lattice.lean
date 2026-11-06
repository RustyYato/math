module

public import Math.Algebra.Semigroup.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace Subsemigroup

variable [Mul α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (Subsemigroup α) α where
  create u hu := {
    toSet := u
    mem_mul := MemMul.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (Subsemigroup α) := latticeBuilder.instCompleteLattice

end Subsemigroup

namespace AddSubsemigroup

variable [Add α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (AddSubsemigroup α) α where
  create u hu := {
    toSet := u
    mem_add := MemAdd.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (AddSubsemigroup α) := latticeBuilder.instCompleteLattice

end AddSubsemigroup
