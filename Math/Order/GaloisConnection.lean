module

public import Math.Order.CompleteLattice.Defs

namespace Math

variable {α β: Type*} [LE α] [LE β]

@[expose] public def GaloisConnection (l: α -> β) (u: β -> α) := ∀a b, l a ≤ b ↔ a ≤ u b

public theorem OrderEquiv.toGc (f: α ≃o β) : GaloisConnection f f.symm := by
  intro a b
  apply Iff.intro
  intro h
  apply map_rel_rev f
  rwa [RelEquiv.symm_apply]
  intro h
  apply map_rel_rev f.symm
  rwa [RelEquiv.apply_symm]

namespace GaloisConnection

variable {l: α -> β} {u: β -> α} (gc: GaloisConnection l u)

attribute [local irreducible] OrderOpp in
public theorem dual (gc: GaloisConnection l u) : GaloisConnection
  (OrderOpp.mk ∘ u ∘ OrderOpp.get)
  (OrderOpp.mk ∘ l ∘ OrderOpp.get) := fun a b => (gc b.get a.get).symm

public theorem le_iff_le (gc: GaloisConnection l u) : l a ≤ b ↔ a ≤ u b := gc _ _

public theorem l_le (gc: GaloisConnection l u) : a ≤ u b -> l a ≤ b := gc.le_iff_le.mpr
public theorem le_u (gc: GaloisConnection l u) : l a ≤ b -> a ≤ u b := gc.le_iff_le.mp

variable [LT α] [LT β]

variable {l: α -> β} {u: β -> α} (gc: GaloisConnection l u)

section Preorder

variable [IsPreorder α] [IsPreorder β]

set_option linter.unusedSectionVars false

public theorem ofMonotone (hu: IsMonotone u) (hl: IsMonotone l) (hul: ∀a, a ≤ u (l a)) (hlu: ∀b, l (u b) ≤ b) : GaloisConnection l u := by
  intro a b
  apply Iff.intro <;> intro h
  apply le_trans
  apply hul; apply hu
  assumption
  apply flip le_trans
  apply hlu; apply hl
  assumption

public theorem le_u_l (gc: GaloisConnection l u) : a ≤ u (l a) := gc.le_u (refl _)
public theorem l_u_le (gc: GaloisConnection l u) : l (u b) ≤ b := gc.l_le (refl _)

public theorem monotone_u (gc: GaloisConnection l u) : IsMonotone u := by
  intro a b h
  apply gc.le_u
  apply le_trans
  apply gc.l_u_le
  assumption
public theorem monotone_l (gc: GaloisConnection l u) : IsMonotone l := gc.dual.monotone_u.dual

public theorem upperBounds_l_image (gc: GaloisConnection l u) (s: Set α) : (s.image l).upperBounds = s.upperBounds.preimage u := by
  ext b; simp
  apply Iff.intro
  intro h x hx
  exact gc.le_u (h x hx)
  intro h x hx
  exact gc.l_le (h x hx)

public theorem lowerBounds_u_image (gc: GaloisConnection l u) (s: Set β) : (s.image u).lowerBounds = s.lowerBounds.preimage l :=
  gc.dual.upperBounds_l_image s

public theorem boundedAbove_l_image (gc: GaloisConnection l u) {s: Set α} : (s.image l).boundedAbove ↔ s.boundedAbove := by
  unfold Set.boundedAbove
  rw [gc.upperBounds_l_image]
  apply Iff.intro
  intro ⟨b, hb⟩
  exists u b
  intro ⟨a, ha⟩
  exists l a
  simp; intro x hx
  apply le_trans
  apply ha; assumption
  apply gc.le_u_l

public theorem boundedBelow_u_image (gc: GaloisConnection l u) {s: Set β} : (s.image u).boundedBelow ↔ s.boundedBelow :=
  gc.dual.boundedAbove_l_image

public theorem le_u_l_trans (gc: GaloisConnection l u) {x y z: α} (h: x ≤ u (l y)) (g: y ≤ u (l z)) : x ≤ u (l z) := by
  apply le_trans h
  apply gc.monotone_u
  apply gc.l_le
  apply g

public theorem le_l_u_trans (gc: GaloisConnection l u) {x y z: β} (h: l (u x) ≤ y) (g: l (u y) ≤ z) : l (u x) ≤ z :=
  gc.dual.le_u_l_trans g h

end Preorder

section PartialOrder

variable [IsPartialOrder α] [IsPreorder β]

public theorem u_l_u_eq_u (gc: GaloisConnection l u) (b: β) : u (l (u b)) = u b := by
  apply le_antisymm
  apply gc.monotone_u
  apply gc.l_u_le
  apply gc.le_u_l

public theorem u_unique {l₀ l₁: α -> β} {u₀ u₁: β -> α}
  (gc₀: GaloisConnection l₀ u₀) (gc₁: GaloisConnection l₁ u₁)
  (hl: ∀i, l₀ i = l₁ i) : ∀i, u₀ i = u₁ i := by
  intro b
  apply le_antisymm
  apply gc₁.le_u
  rw [←hl]
  apply gc₀.l_u_le
  apply gc₀.le_u
  rw [hl]
  apply gc₁.l_u_le

end PartialOrder

section PartialOrder

variable [IsPreorder α] [IsPartialOrder β]

public theorem l_u_l_eq_l (gc: GaloisConnection l u) (a: α) : l (u (l a)) = l a :=
  gc.dual.u_l_u_eq_u a

public theorem l_unique {l₀ l₁: α -> β} {u₀ u₁: β -> α}
  (gc₀: GaloisConnection l₀ u₀) (gc₁: GaloisConnection l₁ u₁)
  (hu: ∀i, u₀ i = u₁ i) : ∀i, l₀ i = l₁ i :=
  gc₀.dual.u_unique gc₁.dual hu

end PartialOrder

section Structures

variable (α: Type*) [LE α] [LT α]

public protected class LawfulTop extends Top α, IsLawfulTop α where
public protected class LawfulBot extends Bot α, IsLawfulBot α where

public protected class SupSemilattice extends Max α, IsSupSemilattice α where
public protected class InfSemilattice extends Min α, IsInfSemilattice α where
public protected class Lattice extends
  GaloisConnection.SupSemilattice α,
  GaloisConnection.InfSemilattice α where

public protected class SupLattice extends
  GaloisConnection.SupSemilattice α,
  SupSet α, IsSupLattice α where
public protected class InfLattice extends
  GaloisConnection.InfSemilattice α,
  InfSet α, IsInfLattice α where
public protected class CompleteLattice extends
  GaloisConnection.SupLattice α,
  GaloisConnection.InfLattice α,
  GaloisConnection.LawfulTop α,
  GaloisConnection.LawfulBot α,
  IsCompleteLattice α where

end Structures

end GaloisConnection
