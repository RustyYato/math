module

public import Math.Algebra.Group.Set.Defs
public import Math.Algebra.Group.Defs.Hom

import Math.Algebra.Semigroup.Set.Hom
import Math.Algebra.Monoid.Set.Hom

namespace Math

namespace MemInv

variable [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]
  [Funlike F α β] [IsMulHom F α β] [IsOneHom F α β]

public theorem preimage [SetLike S β] [IsMemInv S β] (f: F) (s: S) : MemInv (Set.preimage f s) := by
  intro a ha
  show f _ ∈ s; rw [map_inv]
  apply mem_inv <;> assumption

public theorem image [SetLike S α] [IsMemInv S α] (f: F) (s: S) : MemInv (Set.image f s) := by
  intro a ha; simp at *
  obtain ⟨a, ha, rfl⟩ := ha
  exists a⁻¹
  apply And.intro
  exact mem_inv s ha
  rw [map_inv]

end MemInv

namespace MemNeg

variable [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β]
  [Funlike F α β] [IsAddHom F α β] [IsZeroHom F α β]

public theorem preimage [SetLike S β] [IsMemNeg S β] (f: F) (s: S) : MemNeg (Set.preimage f s) := by
  intro a ha
  show f _ ∈ s; rw [map_neg]
  apply mem_neg <;> assumption

public theorem image [SetLike S α] [IsMemNeg S α] (f: F) (s: S) : MemNeg (Set.image f s) := by
  intro a ha; simp at *
  obtain ⟨a, ha, rfl⟩ := ha
  exists -a
  apply And.intro
  exact mem_neg s ha
  rw [map_neg]

end MemNeg

namespace Subgroup

variable {α β: Type*} [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]
  [Funlike F α β] [IsMulHom F α β] [IsOneHom F α β]

@[expose] public def preimage (f: F) (s: Subgroup β) : Subgroup α where
  toSet := Set.preimage f s
  mem_one := by exact MemOne.preimage f s
  mem_inv := by exact MemInv.preimage f s
  mem_mul := by exact MemMul.preimage f s
@[expose] public def image (f: F) (s: Subgroup α) : Subgroup β where
  toSet := Set.image f s
  mem_one := by exact MemOne.image f s
  mem_inv := by exact MemInv.image f s
  mem_mul := by exact MemMul.image f s

@[simp] public theorem mem_preimage {f: F} {s: Subgroup β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Subgroup α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end Subgroup

namespace AddSubgroup

variable {α β: Type*} [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β]
  [Funlike F α β] [IsAddHom F α β] [IsZeroHom F α β]

@[expose] public def preimage (f: F) (s: AddSubgroup β) : AddSubgroup α where
  toSet := Set.preimage f s
  mem_zero := by exact MemZero.preimage f s
  mem_neg := by exact MemNeg.preimage f s
  mem_add := by exact MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubgroup α) : AddSubgroup β where
  toSet := Set.image f s
  mem_zero := by exact MemZero.image f s
  mem_neg := by exact MemNeg.image f s
  mem_add := by exact MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubgroup β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubgroup α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end AddSubgroup
