module

public import Math.Algebra.Semigroup.Set.Defs
public import Math.Algebra.Semigroup.Defs.Hom

namespace Math

namespace MemMul

public theorem preimage
  [Mul α] [Mul β] [Funlike F α β] [IsMulHom F α β]
  [SetLike S β] [IsMemMul S β] (f: F) (s: S) : MemMul (Set.preimage f s) := by
  intro a b ha hb
  show f _ ∈ s; rw [map_mul]
  apply mem_mul <;> assumption

public theorem image
  [Mul α] [Mul β] [Funlike F α β] [IsMulHom F α β]
  [SetLike S α] [IsMemMul S α] (f: F) (s: S) : MemMul (Set.image f s) := by
  intro a b ha hb; simp at *
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  exists a * b
  apply And.intro
  exact mem_mul s ha hb
  rw [map_mul]

end MemMul

namespace MemAdd

public theorem preimage
  [Add α] [Add β] [Funlike F α β] [IsAddHom F α β]
  [SetLike S β] [IsMemAdd S β] (f: F) (s: S) : MemAdd (Set.preimage f s) := by
  intro a b ha hb
  show f _ ∈ s; rw [map_add]
  apply mem_add <;> assumption

public theorem image
  [Add α] [Add β] [Funlike F α β] [IsAddHom F α β]
  [SetLike S α] [IsMemAdd S α] (f: F) (s: S) : MemAdd (Set.image f s) := by
  intro a b ha hb; simp at *
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  exists a + b
  apply And.intro
  exact mem_add s ha hb
  rw [map_add]

end MemAdd

namespace Subsemigroup

variable [Mul α] [Mul β] [Funlike F α β] [IsMulHom F α β]

@[expose] public def preimage (f: F) (s: Subsemigroup β) : Subsemigroup α where
  toSet := Set.preimage f s
  mem_mul := MemMul.preimage f s
@[expose] public def image (f: F) (s: Subsemigroup α) : Subsemigroup β where
  toSet := Set.image f s
  mem_mul := MemMul.image f s

@[simp] public theorem mem_preimage {f: F} {s: Subsemigroup β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Subsemigroup α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end Subsemigroup

namespace AddSubsemigroup

variable [Add α] [Add β] [Funlike F α β] [IsAddHom F α β]

@[expose] public def preimage (f: F) (s: AddSubsemigroup β) : AddSubsemigroup α where
  toSet := Set.preimage f s
  mem_add := MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubsemigroup α) : AddSubsemigroup β where
  toSet := Set.image f s
  mem_add := MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubsemigroup β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubsemigroup α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end AddSubsemigroup
