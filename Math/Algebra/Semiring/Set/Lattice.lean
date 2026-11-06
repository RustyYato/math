module

public import Math.Algebra.Semiring.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace Subsemiring

variable [SemiringOps α] [IsSemiring α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (Subsemiring α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_one := MemOne.copy u hu
    mem_add := MemAdd.copy u hu
    mem_mul := MemMul.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (Subsemiring α) := latticeBuilder.instCompleteLattice

end Subsemiring
