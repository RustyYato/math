module

public import Math.Algebra.Group.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace Subgroup

variable [GroupOps α] [IsGroup α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (Subgroup α) α where
  create u hu := {
    toSet := u
    mem_one := MemOne.copy u hu
    mem_inv := MemInv.copy u hu
    mem_mul := MemMul.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (Subgroup α) := latticeBuilder.instCompleteLattice

end Subgroup

namespace AddSubgroup

variable [AddGroupOps α] [IsAddGroup α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (AddSubgroup α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_neg := MemNeg.copy u hu
    mem_add := MemAdd.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (AddSubgroup α) := latticeBuilder.instCompleteLattice

end AddSubgroup
