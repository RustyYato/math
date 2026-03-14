import LeanMath.Order.GaloisConnection
import LeanMath.Algebra.Semiring.Ideal.TwoSided.Defs

namespace Ideal

variable [SemiringOps α] [IsSemiring α]

local instance : LatticeBuilder (Ideal α) where
  closure := Ideal.closure
  create u hu := {
    toSet := u
    mem_zero := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_zero u
    mem_add := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_add u
    mem_left_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_left_mul u
    mem_right_mul := by
      obtain ⟨u, rfl⟩ := hu
      apply mem_right_mul u
  }
  gc s i := by
    apply Iff.intro
    intro h x hx
    show x ∈ i; apply Ideal.of_mem_closure _ _ _ hx
    apply h
    intro h x hx
    apply h
    apply Ideal.sub_closure
    assumption
  bot := {
    val := ⊥
    property u := Ideal.bot_sub _
  }

open LatticeBuilder
instance : LatticeBuilder.CompleteLattice (Ideal α) :=
  inferInstance

instance : IsCompleteLattice (Ideal α) := inferInstance

end Ideal
