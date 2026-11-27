module

public import Math.Algebra.Monoid.Set.Defs
public import Math.Algebra.Monoid.Defs.Hom

import Math.Algebra.Semigroup.Set.Hom

namespace Math

namespace MemOne

public theorem preimage
  [One α] [One β] [Funlike F α β] [IsOneHom F α β]
  [SetLike S β] [IsMemOne S β] (f: F) (s: S) : MemOne (Set.preimage f s) := by
  show f 1 ∈ s
  rw [map_one]
  apply mem_one

public theorem image
  [One α] [One β] [Funlike F α β] [IsOneHom F α β]
  [SetLike S α] [IsMemOne S α] (f: F) (s: S) : MemOne (Set.image f s) := by
  show 1 ∈ _; simp
  exists 1; exact ⟨mem_one s, map_one _⟩

end MemOne

namespace MemZero

public theorem preimage
  [Zero α] [Zero β] [Funlike F α β] [IsZeroHom F α β]
  [SetLike S β] [IsMemZero S β] (f: F) (s: S) : MemZero (Set.preimage f s) := by
  show f 0 ∈ s
  rw [map_zero]
  apply mem_zero

public theorem image
  [Zero α] [Zero β] [Funlike F α β] [IsZeroHom F α β]
  [SetLike S α] [IsMemZero S α] (f: F) (s: S) : MemZero (Set.image f s) := by
  show 0 ∈ _; simp
  exists 0; exact ⟨mem_zero s, map_zero _⟩

end MemZero

namespace Submonoid

variable [One α] [Mul α] [One β] [Mul β] [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]

@[expose] public def preimage (f: F) (s: Submonoid β) : Submonoid α where
  toSet := Set.preimage f s
  mem_one := by exact MemOne.preimage f s
  mem_mul := by exact MemMul.preimage f s
@[expose] public def image (f: F) (s: Submonoid α) : Submonoid β where
  toSet := Set.image f s
  mem_one := by exact MemOne.image f s
  mem_mul := by exact MemMul.image f s

@[simp] public theorem mem_preimage {f: F} {s: Submonoid β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Submonoid α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end Submonoid

namespace AddSubmonoid

variable [Zero α] [Add α] [Zero β] [Add β] [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]

@[expose] public def preimage (f: F) (s: AddSubmonoid β) : AddSubmonoid α where
  toSet := Set.preimage f s
  mem_zero := by exact MemZero.preimage f s
  mem_add := by exact MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubmonoid α) : AddSubmonoid β where
  toSet := Set.image f s
  mem_zero := by exact MemZero.image f s
  mem_add := by exact MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubmonoid β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubmonoid α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end AddSubmonoid
