import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Algebra.Set

open LatticeBuilder

namespace Subalgebra

variable [SemiringOps R] [SemiringOps α] [IsSemiring R] [IsSemiring α]
  [AlgebraMap R α] [SMul R α] [IsAlgebra R α]

private def closure := span R (α := α)
private def of_mem_closure := of_mem_span (S := Subalgebra R α) (R := R) (α := α)
private def sub_closure := sub_span (R := R) (α := α)

local instance : LatticeBuilder (Subalgebra R α) where
  create u hu := {
    toSet := u
    mem_algebraMap r := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_algebraMap u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_mul u
  }

instance : LatticeBuilder.BundledCompleteLattice (Subalgebra R α) :=
  inferInstance

instance : IsCompleteLattice (Subalgebra R α) := inferInstance

end Subalgebra

namespace NonUnitalSubalgebra

variable [AddMonoidOps R] [AddMonoidOps α] [Mul R] [Mul α]
  [IsNonUnitalNonAssocSemiring R] [IsNonUnitalNonAssocSemiring α]
  [SMul R α] [IsNonUnitalAlgebra R α]

private def closure := span R (α := α)
private def of_mem_closure := of_mem_span (S := NonUnitalSubalgebra R α) (R := R) (α := α)
private def sub_closure := sub_span (R := R) (α := α)

local instance : LatticeBuilder (NonUnitalSubalgebra R α) where
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_mul u
    mem_smul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_smul u
  }

instance : LatticeBuilder.BundledCompleteLattice (NonUnitalSubalgebra R α) :=
  inferInstance

instance : IsCompleteLattice (NonUnitalSubalgebra R α) := inferInstance

end NonUnitalSubalgebra
