module

public import Math.Algebra.Ring.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace Subring

variable [RingOps α] [IsRing α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (Subring α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_one := MemOne.copy u hu
    mem_neg := MemNeg.copy u hu
    mem_add := MemAdd.copy u hu
    mem_mul := MemMul.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (Subring α) := latticeBuilder.instCompleteLattice

end Subring
