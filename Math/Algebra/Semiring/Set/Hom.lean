module

public import Math.Algebra.Semiring.Set.Defs
public import Math.Algebra.Semiring.Defs.Hom

import Math.Algebra.Semigroup.Set.Hom
import Math.Algebra.Monoid.Set.Hom

namespace Math.Subsemiring

variable [Zero α] [One α] [Add α] [Mul α] [Zero β] [One β] [Add β] [Mul β] [Funlike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

@[expose] public def preimage (f: F) (s: Subsemiring β) : Subsemiring α where
  toSet := Set.preimage f s
  mem_zero := by exact MemZero.preimage f s
  mem_one := by exact MemOne.preimage f s
  mem_add := by exact MemAdd.preimage f s
  mem_mul := by exact MemMul.preimage f s
@[expose] public def image (f: F) (s: Subsemiring α) : Subsemiring β where
  toSet := Set.image f s
  mem_zero := by exact MemZero.image f s
  mem_one := by exact MemOne.image f s
  mem_add := by exact MemAdd.image f s
  mem_mul := by exact MemMul.image f s

@[simp] public theorem mem_preimage {f: F} {s: Subsemiring β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Subsemiring α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image
