module

public import Math.Algebra.Module.Set.Defs
public import Math.Algebra.Module.Defs.Hom

import Math.Algebra.Semigroup.Set.Hom
import Math.Algebra.Monoid.Set.Hom

namespace Math.Submodule

variable [Zero α] [Add α] [SMul R α] [Zero β] [Add β] [SMul R β] [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsSMulHom F R α β]

@[expose] public def preimage (f: F) (s: Submodule R β) : Submodule R α where
  toSet := Set.preimage f s
  mem_zero := by exact MemZero.preimage f s
  mem_smul := by exact MemSMul.preimage f s
  mem_add := by exact MemAdd.preimage f s
@[expose] public def image (f: F) (s: Submodule R α) : Submodule R β where
  toSet := Set.image f s
  mem_zero := by exact MemZero.image f s
  mem_smul := by exact MemSMul.image f s
  mem_add := by exact MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: Submodule R β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Submodule R α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image
