module

public import Math.Algebra.Semiring.Ideal.Defs
public import Math.Algebra.Semiring.Defs.Hom

import Math.Algebra.Semigroup.Set.Hom
import Math.Algebra.Monoid.Set.Hom

namespace Math

variable {α β: Type*} [Mul α] [Mul β]

namespace MemMulLeft

public theorem preimage
  [Funlike F α β] [IsMulHom F α β]
  [SetLike S β] [IsMemMulLeft S β] (f: F) (s: S) : MemMulLeft (Set.preimage f s) := by
  intro k a ha
  show f (k * a) ∈ s
  rw [map_mul]; apply mem_mul_left s
  assumption

public theorem image
  [SurjectionLike F α β] [IsMulHom F α β]
  [SetLike S α] [IsMemMulLeft S α] (f: F) (s: S) : MemMulLeft (Set.image f s) := by
  intro k _ ha; simp at ha
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := SurjectionLike.coeSurjection f k
  rw [←map_mul]; apply Set.mem_image'
  apply mem_mul_left s
  assumption

end MemMulLeft

namespace MemMulRight

public theorem preimage
  [Funlike F α β] [IsMulHom F α β]
  [SetLike S β] [IsMemMulRight S β] (f: F) (s: S) : MemMulRight (Set.preimage f s) := by
  intro k a ha
  show f (a * k) ∈ s
  rw [map_mul]; apply mem_mul_right s
  assumption

public theorem image
  [SurjectionLike F α β] [IsMulHom F α β]
  [SetLike S α] [IsMemMulRight S α] (f: F) (s: S) : MemMulRight (Set.image f s) := by
  intro k _ ha; simp at ha
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := SurjectionLike.coeSurjection f k
  rw [←map_mul]; apply Set.mem_image'
  apply mem_mul_right s
  assumption

end MemMulRight

variable {α β: Type*} [Zero α] [Add α] [Mul α] [Zero β] [Add β] [Mul β]

namespace IdealLeft

@[expose] public def preimage
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  (f: F) (s: IdealLeft β) : IdealLeft α where
  toSet := s.toSet.preimage f
  mem_zero := by exact MemZero.preimage f s
  mem_add := by exact MemAdd.preimage f s
  mem_mul_left := MemMulLeft.preimage f s

@[expose] public def image
  [SurjectionLike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  (f: F) (s: IdealLeft α) : IdealLeft β where
  toSet := s.toSet.image f
  mem_zero := by exact MemZero.image f s
  mem_add := by exact MemAdd.image f s
  mem_mul_left := MemMulLeft.image f s

@[simp] public theorem mem_preimage
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  {f: F} {s: IdealLeft β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image
  [SurjectionLike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  {f: F} {s: IdealLeft α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end IdealLeft

namespace IdealRight

@[expose] public def preimage
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  (f: F) (s: IdealRight β) : IdealRight α where
  toSet := s.toSet.preimage f
  mem_zero := by exact MemZero.preimage f s
  mem_add := by exact MemAdd.preimage f s
  mem_mul_right := MemMulRight.preimage f s

@[expose] public def image
  [SurjectionLike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  (f: F) (s: IdealRight α) : IdealRight β where
  toSet := s.toSet.image f
  mem_zero := by exact MemZero.image f s
  mem_add := by exact MemAdd.image f s
  mem_mul_right := MemMulRight.image f s

@[simp] public theorem mem_preimage
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  {f: F} {s: IdealRight β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image
  [SurjectionLike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  {f: F} {s: IdealRight α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end IdealRight

namespace Ideal

@[expose] public def preimage
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  (f: F) (s: Ideal β) : Ideal α where
  toSet := s.toSet.preimage f
  mem_zero := by exact MemZero.preimage f s
  mem_add := by exact MemAdd.preimage f s
  mem_mul_left := MemMulLeft.preimage f s
  mem_mul_right := MemMulRight.preimage f s

@[expose] public def image
  [SurjectionLike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  (f: F) (s: Ideal α) : Ideal β where
  toSet := s.toSet.image f
  mem_zero := by exact MemZero.image f s
  mem_add := by exact MemAdd.image f s
  mem_mul_left := MemMulLeft.image f s
  mem_mul_right := MemMulRight.image f s

@[simp] public theorem mem_preimage
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  {f: F} {s: Ideal β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image
  [SurjectionLike F α β] [IsZeroHom F α β] [IsAddHom F α β] [IsMulHom F α β]
  {f: F} {s: Ideal α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end Ideal
