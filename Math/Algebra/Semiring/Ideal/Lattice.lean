module

public import Math.Algebra.Semiring.Ideal.Defs
public import Math.Order.GaloisConnection

namespace Math

namespace IdealLeft

variable [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (IdealLeft α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_add := MemAdd.copy u hu
    mem_mul_left := MemMulLeft.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (IdealLeft α) := latticeBuilder.instCompleteLattice

end IdealLeft

namespace IdealRight

variable [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (IdealRight α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_add := MemAdd.copy u hu
    mem_mul_right := MemMulRight.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (IdealRight α) := latticeBuilder.instCompleteLattice

end IdealRight

namespace Ideal

variable [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α]

@[instance_reducible]
public def latticeBuilder : LatticeBuilder (Ideal α) α where
  create u hu := {
    toSet := u
    mem_zero := MemZero.copy u hu
    mem_add := MemAdd.copy u hu
    mem_mul_left := MemMulLeft.copy u hu
    mem_mul_right := MemMulRight.copy u hu
  }

public instance : LatticeBuilder.CompleteLattice (Ideal α) := latticeBuilder.instCompleteLattice

end Ideal
