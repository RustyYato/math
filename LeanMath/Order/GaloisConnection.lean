import LeanMath.Order.CompleteLattice
import LeanMath.Order.Monotone
import LeanMath.Order.Set

variable {α β : Type*} [LT α] [LE α] [LT β] [LE β]

def GaloisConnection (l: α -> β) (u: β -> α) :=
  ∀a b, l a ≤ b ↔ a ≤ u b

class HasCanonicalGc (α β: Type*) [LE α] [LE β] where
  l: α -> β
  u: β -> α
  gc: GaloisConnection l u

def OrderEquiv.toGc (f: α ≃o β) : GaloisConnection f f.symm := by
  intro a b
  rw [map_le f]
  simp

namespace GaloisConnection

variable {l : α → β} {u : β → α} (gc : GaloisConnection l u)

section IsPreorder

variable [IsPreorder α] [IsPreorder β]

def ofMonotone (hu: Monotone u) (hl: Monotone l) (hul: ∀a, a ≤ u (l a)) (hlu: ∀b, l (u b) ≤ b) : GaloisConnection l u := by
  intro a b
  apply Iff.intro
  · intro h
    apply flip le_trans
    apply hu
    assumption
    apply hul
  · intro h
    apply le_trans
    apply hl
    assumption
    apply hlu

def dual : GaloisConnection
  (OrderOpp.mk ∘ u ∘ OrderOpp.get)
  (OrderOpp.mk ∘ l ∘ OrderOpp.get) := fun a b => (gc b a).symm

def le_iff_le {a : α} {b : β} : l a ≤ b ↔ a ≤ u b :=
  gc _ _

def l_le {a : α} {b : β} : a ≤ u b → l a ≤ b :=
  (gc _ _).mpr

def le_u {a : α} {b : β} : l a ≤ b → a ≤ u b :=
  (gc _ _).mp

def le_u_l (a) : a ≤ u (l a) :=
  gc.le_u <| (le_refl _)

def l_u_le (a) : l (u a) ≤ a :=
  gc.l_le <| (le_refl _)

def monotone_u : Monotone u := by
  intro x y le
  apply gc.le_u
  apply le_trans
  apply gc.l_u_le
  assumption

def monotone_l : Monotone l :=
  gc.dual.monotone_u.dual

def upperBounds_l_image (gc : GaloisConnection l u) (s : Set α) : Set.upperBounds (s.image l) = (Set.upperBounds s).preimage u := by
    ext x
    apply Iff.intro
    · intro hx y hy
      apply gc.le_u
      apply hx
      exact Set.mem_image' hy
    · rintro hx _ ⟨y, hy, rfl⟩
      apply gc.l_le
      apply hx
      assumption

def lowerBounds_u_image (gc : GaloisConnection l u) (s : Set β) :
    Set.lowerBounds (s.image u) = (Set.lowerBounds s).preimage l :=
  gc.dual.upperBounds_l_image s

def boundedAbove_l_image {s : Set α} : Set.BoundedAbove (s.image l) ↔ Set.BoundedAbove s := by
  apply Iff.intro
  intro ⟨b, hb⟩
  exists u b
  intro a ha
  apply gc.le_u
  apply hb
  apply Set.mem_image'
  assumption
  intro ⟨a, ha⟩
  exists l a
  rintro _ ⟨b, hb, rfl⟩
  apply gc.monotone_l
  apply ha
  assumption

def boundedBelow_u_image {s : Set β} : Set.BoundedBelow (s.image u) ↔ Set.BoundedBelow s :=
  gc.dual.boundedAbove_l_image

def le_u_l_trans {x y z : α} (hxy : x ≤ u (l y)) (hyz : y ≤ u (l z)) : x ≤ u (l z) :=
  le_trans hxy (gc.monotone_u <| gc.l_le hyz)

def l_u_le_trans {x y z : β} (hxy : l (u x) ≤ y) (hyz : l (u y) ≤ z) : l (u x) ≤ z :=
  le_trans (gc.monotone_l <| gc.le_u hxy) hyz

end IsPreorder

section IsPartialOrder

variable [IsPartialOrder α] [IsPreorder β]

def u_l_u_eq_u (b : β) : u (l (u b)) = u b := by
  apply le_antisymm
  apply gc.monotone_u
  apply gc.l_u_le
  apply gc.le_u
  rfl

def u_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hl : ∀ a, l a = l' a)
    {b : β} : u b = u' b :=
  le_antisymm (gc'.le_u <| hl (u b) ▸ gc.l_u_le _) (gc.le_u <| (hl (u' b)).symm ▸ gc'.l_u_le _)

def u_eq (gc : GaloisConnection l u) {z : α} {y : β} : u y = z ↔ ∀ x, x ≤ z ↔ l x ≤ y := by
  apply Iff.intro
  intro h x
  rw [←h, gc]
  intro h
  apply le_antisymm
  apply (h _).mpr
  apply gc.l_u_le
  apply gc.le_u
  apply (h _).mp
  rfl

end IsPartialOrder

section IsPartialOrder

variable [IsPreorder α] [IsPartialOrder β]

def l_u_l_eq_l (a : α) : l (u (l a)) = l a :=
  gc.dual.u_l_u_eq_u _

def l_unique {l' : α → β} {u' : β → α} (gc' : GaloisConnection l' u') (hu : ∀ b, u b = u' b)
    {a : α} : l a = l' a := gc.dual.u_unique gc'.dual hu

def l_eq {x : α} {z : β} : l x = z ↔ ∀ y, z ≤ y ↔ x ≤ u y := gc.dual.u_eq

end IsPartialOrder

section IsLawfulTop

variable [IsPartialOrder α] [IsPreorder β] [Top α] [Top β] [IsLawfulTop α] [IsLawfulTop β]

def u_eq_top {x} : u x = ⊤ ↔ l ⊤ ≤ x := by
  rw [gc.u_eq]
  simp [le_top]
  apply Iff.intro
  intro h
  apply h
  intro h y
  apply le_trans _ h
  apply gc.monotone_l
  apply le_top

def u_top : u ⊤ = ⊤ := gc.u_eq_top.mpr (le_top _)

end IsLawfulTop

section IsLawfulTop

variable [IsPartialOrder α] [IsPreorder β] [Top β] [IsLawfulTop β]

class LawfulTop (gc: GaloisConnection l u) extends Top α, IsLawfulTop α where

scoped instance (priority := 1) instLawfulTop : LawfulTop gc where
  top := u ⊤
  le_top _ := by
    apply gc.le_u
    apply le_top

end IsLawfulTop

section IsLawfulBot

variable [IsPreorder α] [IsPartialOrder β] [Bot α] [Bot β] [IsLawfulBot α] [IsLawfulBot β]

def l_eq_bot {x} : l x = ⊥ ↔ x ≤ u ⊥ := by
  rw [gc.l_eq]
  simp [bot_le]
  apply Iff.intro
  intro h
  apply h
  intro h y
  apply le_trans h
  apply gc.monotone_u
  apply bot_le

def l_bot : l ⊥ = ⊥ := gc.l_eq_bot.mpr (bot_le _)

end IsLawfulBot

section IsLawfulBot

variable [IsPreorder α] [IsPartialOrder β] [Bot α] [IsLawfulBot α]

class LawfulBot (gc: GaloisConnection l u) extends Bot β, IsLawfulBot β where

scoped instance (priority := 1) instLawfllBot : LawfulBot gc where
  bot := l ⊥
  bot_le _ := by
    apply gc.l_le
    apply bot_le

end IsLawfulBot

section SemilatticeMax

variable [Max α] [Max β] [IsSemiLatticeMax α] [IsSemiLatticeMax β]

def l_max : l (a₁ ⊔ a₂) = l a₁ ⊔ l a₂ := by
  apply le_antisymm
  apply gc.l_le
  apply max_le <;> apply gc.le_u
  apply left_le_max
  apply right_le_max
  apply max_le <;> apply gc.monotone_l
  apply left_le_max
  apply right_le_max

end SemilatticeMax

section SemilatticeMin

variable [Min α] [Min β] [IsSemiLatticeMin α] [IsSemiLatticeMin β]

def u_min : u (a₁ ⊓ a₂) = u a₁ ⊓ u a₂ := gc.dual.l_max

end SemilatticeMin

end GaloisConnection

structure GaloisInsertion (l: α -> β) (u: β -> α) where
  gc: GaloisConnection l u
  le_l_u: ∀x, x ≤ l (u x)
  -- this gives a more optimized version of l,
  -- with the knowldege that x is sufficiently large
  choice : ∀x, u (l x) ≤ x -> β := fun x _ => l x
  choice_eq : ∀x h, choice x h = l x := by intros; rfl

structure GaloisCoinsertion (l : α → β) (u : β → α) where
  gc : GaloisConnection l u
  u_l_le : ∀ x, u (l x) ≤ x
  -- this gives a more optimized version of u,
  -- with the knowldege that x is sufficiently small
  choice : ∀ x : β, x ≤ l (u x) → α := fun x _ => u x
  choice_eq : ∀ a h, choice a h = u a := by intros; rfl

variable {l: α -> β} {u: β -> α}

abbrev GaloisInsertion.dual (gi: GaloisInsertion l u) : GaloisCoinsertion
  (OrderOpp.mk ∘ u ∘ OrderOpp.get)
  (OrderOpp.mk ∘ l ∘ OrderOpp.get) where
  gc := gi.gc.dual
  u_l_le := gi.le_l_u
  choice := gi.choice
  choice_eq := gi.choice_eq

abbrev GaloisCoinsertion.dual (gi: GaloisCoinsertion l u) : GaloisInsertion
  (OrderOpp.mk ∘ u ∘ OrderOpp.get)
  (OrderOpp.mk ∘ l ∘ OrderOpp.get) where
  gc := gi.gc.dual
  le_l_u := gi.u_l_le
  choice := gi.choice
  choice_eq := gi.choice_eq

namespace GaloisInsertion

end GaloisInsertion
