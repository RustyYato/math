module

public import Math.Algebra.AddMonoidWithOne.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace AddSubmonoidWithOne

variable [AddMonoidOps α] [NatCast α] [One α] [IsAddMonoidWithOne α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (AddSubmonoidWithOne α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_one := MemOne.copy u hu
    mem_add := MemAdd.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (AddSubmonoidWithOne α) := latticeBuilder.instCompleteLattice

end AddSubmonoidWithOne
