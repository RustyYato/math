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

public theorem l_u_le_trans (gc: GaloisConnection l u) {x y z: β} (h: l (u x) ≤ y) (g: l (u y) ≤ z) : l (u x) ≤ z :=
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

public structure GaloisInsertion (l: α -> β) (u: β -> α) where
  gc: GaloisConnection l u
  le_l_u : ∀x, x ≤ l (u x)
  -- give an optimized version of l, when we know that x is sufficiently large
  choice (x: α) (h: u (l x) ≤ x) : β := l x
  choice_eq (x: α) (h: u (l x) ≤ x) : choice x h = l x := by intros; rfl

public structure GaloisCoinsertion (l: α -> β) (u: β -> α) where
  gc: GaloisConnection l u
  u_l_le : ∀x, u (l x) ≤ x
  -- give an optimized version of u, when we know that x is sufficiently small
  choice (x: β) (h: x ≤ l (u x)) : α := u x
  choice_eq (x: β) (h: x ≤ l (u x)) : choice x h = u x := by intros; rfl

variable {α β: Type*}
  [LE α] [LE β]
  {l: α -> β} {u: β -> α}

@[expose] public def GaloisInsertion.dual (gi: GaloisInsertion l u) : GaloisCoinsertion (OrderOpp.mk ∘ u ∘ OrderOpp.get) (OrderOpp.mk ∘ l ∘ OrderOpp.get) where
  gc := gi.gc.dual
  u_l_le := gi.le_l_u
  choice := gi.choice
  choice_eq := gi.choice_eq

@[expose] public def GaloisCoinsertion.dual (gi: GaloisCoinsertion l u) : GaloisInsertion (OrderOpp.mk ∘ u ∘ OrderOpp.get) (OrderOpp.mk ∘ l ∘ OrderOpp.get) where
  gc := gi.gc.dual
  le_l_u := gi.u_l_le
  choice := gi.choice
  choice_eq := gi.choice_eq

variable [LT α] [LT β]
namespace GaloisInsertion

public abbrev instSupSemilattice [IsPartialOrder β] [Max α] [IsSupSemilattice α] (gi: GaloisInsertion l u) : GaloisConnection.SupSemilattice β where
  toIsPartialOrder := inferInstance
  max a b := l (u a ⊔ u b)
  max_le {k a b} ak bk := by
    show l _ ≤ _
    apply gi.gc.l_le
    apply max_le <;> (apply gi.gc.monotone_u; assumption)
  left_le_max a b := by
    show _ ≤ l _
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply left_le_max
  right_le_max a b := by
    show _ ≤ l _
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply right_le_max

public abbrev instInfSemilattice [IsPartialOrder β] [Min α] [IsInfSemilattice α] (gi: GaloisInsertion l u) : GaloisConnection.InfSemilattice β where
  toIsPartialOrder := inferInstance
  min a b := gi.choice (u a ⊓ u b) <| by
    apply le_min
    all_goals
      apply gi.gc.monotone_u
      apply gi.gc.l_le
    apply min_le_left
    apply min_le_right
  le_min {k a b} ka kb := by
    show k ≤ gi.choice _ _
    rw [gi.choice_eq]
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_min
    all_goals
    apply gi.gc.monotone_u
    assumption
  min_le_left a b := by
    show gi.choice _ _ ≤ _
    rw [gi.choice_eq]
    apply gi.gc.l_le
    apply min_le_left
  min_le_right a b := by
    show gi.choice _ _ ≤ _
    rw [gi.choice_eq]
    apply gi.gc.l_le
    apply min_le_right

public abbrev instLattice [IsPartialOrder β] [Max α] [Min α] [IsLattice α] (gi: GaloisInsertion l u) : GaloisConnection.Lattice β :=
  { gi.instSupSemilattice, gi.instInfSemilattice with }

public abbrev instLawfulTop [IsPreorder β] [Top α] [IsLawfulTop α] [IsPreorder α] (gi: GaloisInsertion l u) : GaloisConnection.LawfulTop β where
  top := gi.choice ⊤ <| by apply le_top
  le_top b := by
    show _ ≤ gi.choice _ _
    rw [gi.choice_eq]
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_top

public abbrev instLawfulBot [IsPreorder β] [Bot α] [IsLawfulBot α] [IsPreorder α] (gi: GaloisInsertion l u) : GaloisConnection.LawfulBot β where
  bot := l ⊥
  bot_le a := by
    apply gi.gc.l_le
    apply bot_le

public abbrev instSupLattice [IsPartialOrder β] [Max α] [SupSet α] [IsSupLattice α] (gi: GaloisInsertion l u) : GaloisConnection.SupLattice β where
  toSupSemilattice := gi.instSupSemilattice
  sSup S := l (⨆ (S.image u))
  le_sSup S := by
    show l _ ∈ _; intro b b_in_S
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_sSup
    apply Set.mem_image'
    assumption
  sSup_le U := by
    show l _ ∈ _; intro b b_in_ub
    apply gi.gc.l_le
    apply sSup_le
    intro x hx; simp at hx
    obtain ⟨x, hx, rfl⟩ := hx
    apply gi.gc.monotone_u
    apply b_in_ub
    assumption

public abbrev instInfLattice [IsPartialOrder β] [Min α] [InfSet α] [IsInfLattice α] (gi: GaloisInsertion l u) : GaloisConnection.InfLattice β where
  toInfSemilattice := gi.instInfSemilattice
  sInf S := gi.choice (⨅ (S.image u)) <| by
    apply le_sInf
    intro x hx; simp at hx
    obtain ⟨x, hx, rfl⟩ := hx
    apply gi.gc.monotone_u
    apply gi.gc.l_le
    apply sInf_le
    apply Set.mem_image'
    assumption
  sInf_le S := by
    show gi.choice _ _ ∈ _; intro b b_in_S
    rw [gi.choice_eq]
    apply gi.gc.l_le
    apply sInf_le
    apply Set.mem_image'
    assumption
  le_sInf U := by
    show gi.choice _ _ ∈ _; intro b b_in_lb
    rw [gi.choice_eq]
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_sInf
    intro x hx; simp at hx
    obtain ⟨x, hx, rfl⟩ := hx
    apply gi.gc.monotone_u
    apply b_in_lb
    assumption

public abbrev instCompleteLattice [IsPartialOrder β] [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α] (gi: GaloisInsertion l u) : GaloisConnection.CompleteLattice β :=
  { gi.instLawfulTop, gi.instLawfulBot, gi.instSupLattice, gi.instInfLattice with }

end GaloisInsertion

public class LatticeBuilder (S α: Type*) [SetLike S α] where
  protected closure: Set α -> S := by exact closure
  protected create : ∀u: Set α, (∃s: S, u = s) -> S
  protected create_eq (s: S) : create s ⟨_, rfl⟩ = s := by intros; rfl
  protected gc: ∀(s: Set α) (t: S), s ⊆ t ↔ closure s ⊆ t := by
    intro s i
    apply Iff.intro
    intro h x hx
    show x ∈ i; apply of_mem_closure _ _ _ hx
    apply h
    intro h x hx
    apply h
    apply sub_closure
    assumption
  protected bot : S := by exact ⊥
  protected bot_spec (s: Set α) : bot ⊆ closure s := by exact bot_sub

namespace LatticeBuilder

variable {S α: Type*} [SetLike S α] [LatticeBuilder S α]

public scoped instance : LE S where
  le a b := (a: Set α) ≤ (b: Set α)
public scoped instance : LT S where
  lt a b := (a: Set α) < (b: Set α)

public scoped instance : IsPartialOrder S where
  lt_iff_le_and_not_ge := Iff.rfl
  refl _ := Set.sub_refl _
  htrans := Set.sub_trans
  antisymm _ _ h g := Set.coe_inj (Set.sub_antisymm h g)

theorem le_closure (s: Set α) : s ≤ ((LatticeBuilder.closure s: S): Set α) := by
  apply (LatticeBuilder.gc (S := S) s _).mpr
  apply Set.sub_refl

theorem closure_eq (s: S) : s = LatticeBuilder.closure (s: Set α) := by
  apply le_antisymm
  apply le_closure
  apply (LatticeBuilder.gc _ _).mp
  apply Set.sub_refl

@[expose] public def giGenerate : @GaloisInsertion (Set α) S _ _ LatticeBuilder.closure Set.coe where
  gc _ _ := (LatticeBuilder.gc _ _).symm
  le_l_u s := by apply le_closure
  choice x hx := LatticeBuilder.create x (by
    exists LatticeBuilder.closure x
    apply le_antisymm
    apply le_closure
    assumption)
  choice_eq x hx := by
    apply flip Eq.trans
    apply LatticeBuilder.create_eq (S := S) (α := α)
    congr
    apply le_antisymm
    apply le_closure
    assumption

public protected class CompleteLattice (α: Type*) extends LE α, LT α, IsPartialOrder α, GaloisConnection.CompleteLattice α where

public instance : LatticeBuilder.CompleteLattice S where
  toCompleteLattice := {
    (giGenerate (S := S) (α := α)).instCompleteLattice with
    bot := LatticeBuilder.bot α
    bot_le := by
      intro s
      apply le_trans
      apply LatticeBuilder.bot_spec s
      rw [←LatticeBuilder.closure_eq]
  }

end LatticeBuilder
