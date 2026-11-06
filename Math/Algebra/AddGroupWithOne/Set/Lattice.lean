module

public import Math.Algebra.AddGroupWithOne.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace AddSubgroupWithOne

variable [AddGroupOps α] [NatCast α] [IntCast α] [One α] [IsAddGroupWithOne α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (AddSubgroupWithOne α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_one := MemOne.copy u hu
    mem_neg := MemNeg.copy u hu
    mem_add := MemAdd.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (AddSubgroupWithOne α) := latticeBuilder.instCompleteLattice

end AddSubgroupWithOne
