module

public import Math.Algebra.AddGroupWithOne.Set.Defs
public import Math.Algebra.AddGroupWithOne.Defs.Hom

import Math.Algebra.Semigroup.Set.Hom
import Math.Algebra.Monoid.Set.Hom
import Math.Algebra.Group.Set.Hom

namespace Math.AddSubgroupWithOne

variable {α β: Type*} [AddGroupOps α] [One α] [IsAddGroup α] [AddGroupOps β] [One β] [IsAddGroup β]
  [Funlike F α β] [IsAddHom F α β] [IsZeroHom F α β] [IsOneHom F α β]

@[expose] public def preimage (f: F) (s: AddSubgroupWithOne β) : AddSubgroupWithOne α where
  toSet := Set.preimage f s
  mem_zero := by exact MemZero.preimage f s
  mem_one := by exact MemOne.preimage f s
  mem_neg := by exact MemNeg.preimage f s
  mem_add := by exact MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubgroupWithOne α) : AddSubgroupWithOne β where
  toSet := Set.image f s
  mem_zero := by exact MemZero.image f s
  mem_one := by exact MemOne.image f s
  mem_neg := by exact MemNeg.image f s
  mem_add := by exact MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubgroupWithOne β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubgroupWithOne α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image
