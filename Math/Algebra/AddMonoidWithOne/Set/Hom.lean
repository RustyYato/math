module

public import Math.Algebra.AddMonoidWithOne.Set.Defs
public import Math.Algebra.AddMonoidWithOne.Defs.Hom

import Math.Algebra.Semigroup.Set.Hom
import Math.Algebra.Monoid.Set.Hom

namespace Math.AddSubmonoidWithOne

variable [Zero α] [One α] [Add α] [Zero β] [One β] [Add β] [Funlike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β]

@[expose] public def preimage (f: F) (s: AddSubmonoidWithOne β) : AddSubmonoidWithOne α where
  toSet := Set.preimage f s
  mem_zero := by exact MemZero.preimage f s
  mem_one := by exact MemOne.preimage f s
  mem_add := by exact MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubmonoidWithOne α) : AddSubmonoidWithOne β where
  toSet := Set.image f s
  mem_zero := by exact MemZero.image f s
  mem_one := by exact MemOne.image f s
  mem_add := by exact MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubmonoidWithOne β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubmonoidWithOne α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image
