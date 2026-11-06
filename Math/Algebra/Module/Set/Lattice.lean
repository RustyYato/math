module

public import Math.Algebra.Module.Set.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace Submodule

variable [AddMonoidOps α] [IsAddMonoid α] [SMul R α] [IsLawfulSMulZero R α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (Submodule R α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_smul := MemSMul.copy u hu
    mem_add := MemAdd.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (Submodule R α) := latticeBuilder.instCompleteLattice

end Submodule
