import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Monoid.Action.Set

open LatticeBuilder

namespace Submodule

variable [Zero α] [Add α] [SMul R α] [IsLawfulZeroAdd α] [IsLawfulSMulZero R α]

private def closure := span R (α := α)
private def of_mem_closure := of_mem_span (S := Submodule R α) (R := R) (α := α)
private def sub_closure := sub_span (R := R) (α := α)

local instance : LatticeBuilder (Submodule R α) where
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_smul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_smul u
  }

instance : LatticeBuilder.CompleteLattice (Submodule R α) :=
  inferInstance

instance : IsCompleteLattice (Submodule R α) := inferInstance

end Submodule
