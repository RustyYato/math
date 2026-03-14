import LeanMath.Order.CompleteLattice
import LeanMath.Order.Monotone
import LeanMath.Order.Set
import LeanMath.Data.Set.Order

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

-- variable [IsPartialOrder α] [IsPreorder β] [Top β] [IsLawfulTop β]

-- class LawfulTop (gc: GaloisConnection l u) extends Top α, IsLawfulTop α where

-- scoped instance (priority := 1) instLawfulTop : LawfulTop gc where
--   top := u ⊤
--   le_top _ := by
--     apply gc.le_u
--     apply le_top

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

-- variable [IsPreorder α] [IsPartialOrder β] [Bot α] [IsLawfulBot α]

-- class LawfulBot (gc: GaloisConnection l u) extends Bot β, IsLawfulBot β where

-- scoped instance (priority := 1) instLawfulBot : LawfulBot gc where
--   bot := l ⊥
--   bot_le _ := by
--     apply gc.l_le
--     apply bot_le

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

section Structures

-- all of these classes should not be used directly as bounds

variable (α: Type*) [LE α] [LT α] [IsPartialOrder α]

protected class LawfulTop extends Top α, IsLawfulTop α where
protected class LawfulBot extends Bot α, IsLawfulBot α where

protected class SemilatticeMax extends
  Max α, IsSemiLatticeMax α where
protected class SemilatticeMin extends
  Min α, IsSemiLatticeMin α where
protected class Lattice extends
  GaloisConnection.SemilatticeMax α, GaloisConnection.SemilatticeMin α where

protected class CompleteSemilatticeSup extends
  GaloisConnection.SemilatticeMax α,
  GaloisConnection.LawfulTop α,
  GaloisConnection.LawfulBot α,
  SupSet α, IsCompleteSemilatticeSup α where
protected class CompleteSemilatticeInf extends
  GaloisConnection.SemilatticeMin α,
  GaloisConnection.LawfulTop α,
  GaloisConnection.LawfulBot α,
  InfSet α, IsCompleteSemilatticeInf α  where

protected class CompleteLattice extends
  GaloisConnection.CompleteSemilatticeSup α,
  GaloisConnection.CompleteSemilatticeInf α,
  IsCompleteLattice α where

end Structures

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

abbrev GaloisInsertion.instSemilatticeMax [Max α] [IsPartialOrder β] [IsSemiLatticeMax α] (gi: GaloisInsertion l u) : GaloisConnection.SemilatticeMax β where
  max a b := l (u a ⊔ u b)
  left_le_max {a b} := by
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply left_le_max
  right_le_max {a b} := by
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply right_le_max
  max_le {x a b} ha hb := by
    apply gi.gc.l_le
    apply max_le <;> (apply gi.gc.monotone_u; assumption)
abbrev GaloisInsertion.instSemilatticeMin [Min α] [IsPartialOrder β] [IsSemiLatticeMin α] (gi: GaloisInsertion l u) : GaloisConnection.SemilatticeMin β where
  min a b := gi.choice (u a ⊓ u b) <| by
    apply le_min <;> (apply gi.gc.monotone_u; apply gi.gc.l_le)
    apply min_le_left
    apply min_le_right
  min_le_left {a b}:= by
    rw [gi.choice_eq]
    apply gi.gc.l_le
    apply min_le_left
  min_le_right {a b}:= by
    rw [gi.choice_eq]
    apply gi.gc.l_le
    apply min_le_right
  le_min {x a b} ha hb := by
    rw [gi.choice_eq]
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_min <;> (apply gi.gc.monotone_u; assumption)

abbrev GaloisInsertion.liftLattice [Min α] [Max α] [IsPartialOrder β] [IsLattice α] (gi: GaloisInsertion l u) : GaloisConnection.Lattice β :=
  { gi.instSemilatticeMax, gi.instSemilatticeMin with }


abbrev GaloisInsertion.instLawfulTop [Top α] [IsLawfulTop α] [IsPreorder α] [IsPreorder β] (gi : GaloisInsertion l u) : GaloisConnection.LawfulTop β where
  top := gi.choice ⊤ (le_top _)
  le_top x := by
    show _ ≤ gi.choice ⊤ (le_top _)
    rw [gi.choice_eq]
    apply le_trans
    apply gi.le_l_u
    apply gi.gc.monotone_l
    apply le_top

abbrev GaloisInsertion.instLawfulBot [Bot α] [IsLawfulBot α] [IsPreorder α] [IsPreorder β] (gi : GaloisInsertion l u) : GaloisConnection.LawfulBot β where
  bot := l ⊥
  bot_le x := by
    apply gi.gc.l_le
    apply bot_le

abbrev GaloisInsertion.liftCompleteSemilatticeSup
  [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α]
  [IsPartialOrder β] (gi : GaloisInsertion l u) : GaloisConnection.CompleteSemilatticeSup β := {
    gi.liftLattice, gi.instLawfulTop, gi.instLawfulBot with
    sSup S := l <| ⨆ (S.image u)
    sSup_le S b h := by
      apply gi.gc.l_le
      apply sSup_le
      rintro _ ⟨a, _, rfl⟩
      apply gi.gc.monotone_u
      apply h
      assumption
    le_sSup S b hb := by
      apply le_trans
      apply gi.le_l_u
      apply gi.gc.monotone_l
      apply le_sSup
      apply Set.mem_image'
      assumption
  }

abbrev GaloisInsertion.liftCompleteSemilatticeInf
  [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α]
  [IsPartialOrder β] (gi : GaloisInsertion l u) : GaloisConnection.CompleteSemilatticeInf β := {
    gi.liftLattice, gi.instLawfulTop, gi.instLawfulBot with
    sInf S := gi.choice (⨅ (S.image u)) <| by
      apply le_sInf
      rintro _ ⟨b, hb, rfl⟩
      apply gi.gc.monotone_u
      apply gi.gc.l_le
      apply sInf_le
      apply Set.mem_image'
      assumption
    le_sInf S b h := by
      rw [gi.choice_eq]
      apply le_trans
      apply gi.le_l_u
      apply gi.gc.monotone_l
      apply le_sInf
      rintro _ ⟨a, _, rfl⟩
      apply gi.gc.monotone_u
      apply h
      assumption
    sInf_le S b hb := by
      rw [gi.choice_eq]
      apply gi.gc.l_le
      apply sInf_le
      apply Set.mem_image'
      assumption
  }

abbrev GaloisInsertion.liftCompleteLattice
  [Max α] [Min α] [SupSet α] [InfSet α] [Top α] [Bot α] [IsCompleteLattice α]
  [IsPartialOrder β] (gi : GaloisInsertion l u) : GaloisConnection.CompleteLattice β := {
    gi.liftCompleteSemilatticeSup, gi.liftCompleteSemilatticeInf with
  }

class LatticeBuilder (S: Type*) {α: outParam <| Type*} [SetLike S α] where
  protected closure: Set α -> S := by exact closure
  protected create: ∀u: Set α, (∃s: S, u = s) -> S
  protected create_spec: ∀(u: Set α) (h), create u h = u := by intros; rfl
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
  protected bot : { bot: S // ∀s, bot ⊆ closure s } := by exact {
    val := ⊥
    property u := bot_sub _
  }

namespace LatticeBuilder

variable [SetLike S α] [LatticeBuilder S]

local instance instLE : LE S where
  le a b := a ⊆ b
local instance instLT : LT S where
  lt a b := a ≤ b ∧ ¬b ≤ a

local instance : IsPartialOrder S where
  lt_iff_le_and_not_ge := Iff.rfl
  refl _ := Set.sub_refl _
  trans := Set.sub_trans
  antisymm ha hb := SetLike.coeInj (Set.sub_antisymm ha hb)

private def closure_ge: ∀s: Set α, s ≤ LatticeBuilder.closure (S := S) s := by
  intro s
  apply (LatticeBuilder.gc s _).mpr
  apply Set.sub_refl

private def closure_eq (s: S) : s = LatticeBuilder.closure s := by
  apply SetLike.coeInj
  apply Set.sub_antisymm
  · apply (LatticeBuilder.gc _ _).mpr
    apply Set.sub_refl
  · apply (LatticeBuilder.gc _ _).mp
    apply Set.sub_refl

def giGenerate : @GaloisInsertion (Set α) S _ _ LatticeBuilder.closure (fun x => x) where
  gc _ _ := (LatticeBuilder.gc _ _).symm
  le_l_u _ := closure_ge _
  choice s hs := LatticeBuilder.create s <| by
    exists LatticeBuilder.closure s
    exact le_antisymm (closure_ge s) hs
  choice_eq := by
    intro s hs
    have := le_antisymm (closure_ge s) hs
    apply SetLike.coeInj; simp
    rwa [LatticeBuilder.create_spec s ⟨_, this⟩]

protected class CompleteLattice (α: Type*) extends
  LE α, LT α, IsPartialOrder α,
  GaloisConnection.CompleteLattice α where

scoped instance toCompleteLattice : LatticeBuilder.CompleteLattice S where
  toCompleteLattice := {
    giGenerate.liftCompleteLattice with
    bot := LatticeBuilder.bot.val
    bot_le s := by
      rw [LatticeBuilder.closure_eq s]
      apply LatticeBuilder.bot.property
  }

end LatticeBuilder
