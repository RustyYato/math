module

public import Math.Order.Relation.Defs
public import Math.Data.OfEquiv.Defs
public import Math.Order.TopBot.Defs
public import Math.Order.Opposite
public import Math.Tactic.Basic
public import Math.Logic.LEM

namespace Math

@[expose] section Property

public class IsLawfulLT (α: Type*) [LE α] [LT α] where
  lt_iff_le_and_not_ge {a b: α} : a < b ↔ a ≤ b ∧ ¬(b ≤ a)
export IsLawfulLT (lt_iff_le_and_not_ge)
public class IsPreorder (α: Type*) [LE α] [LT α] extends IsLawfulLT α, IsRefl (α := α) (· ≤ ·), IsTrans (α := α) (· ≤ ·) where
public class IsPartialOrder (α: Type*) [LE α] [LT α] extends IsPreorder α, IsAntisymm (α := α) (· ≤ ·) (· = ·) where
public class IsLinearOrder (α: Type*) [LE α] [LT α] extends IsPartialOrder α, IsConnected (α := α) (· < ·) (· = ·) where

infixl:68 " ⊔ " => max
infixl:69 " ⊓ " => min

public class IsLawfulMax (α: Type*) [Max α] [LE α] where
  left_le_max (a b: α) : a ≤ a ⊔ b
  right_le_max (a b: α) : b ≤ a ⊔ b
public class IsLawfulMin (α: Type*) [Min α] [LE α] where
  min_le_left (a b: α) : a ⊓ b ≤ a
  min_le_right (a b: α) : a ⊓ b ≤ b

export IsLawfulMax (left_le_max right_le_max)
export IsLawfulMin (min_le_left min_le_right)

public class SupSemilatticeOps (α: Type*) extends Max α, LE α, LT α where
public class InfSemilatticeOps (α: Type*) extends Min α, LE α, LT α where
public class LatticeOps (α: Type*) extends SupSemilatticeOps α, InfSemilatticeOps α where

public instance [Max α] [LE α] [LT α] : SupSemilatticeOps α where
public instance [Min α] [LE α] [LT α] : InfSemilatticeOps α where
public instance [Max α] [Min α] [LE α] [LT α] : LatticeOps α where

public class IsSupSemilattice (α: Type*) [SupSemilatticeOps α] extends IsPartialOrder α, IsLawfulMax α where
  max_le {k a b: α} : a ≤ k -> b ≤ k -> a ⊔ b ≤ k
public class IsInfSemilattice (α: Type*) [InfSemilatticeOps α] extends IsPartialOrder α, IsLawfulMin α where
  le_min {k a b: α} : k ≤ a -> k ≤ b -> k ≤ a ⊓ b

export IsSupSemilattice (max_le)
export IsInfSemilattice (le_min)

public class IsLattice (α: Type*) [LatticeOps α] extends IsSupSemilattice α, IsInfSemilattice α where

variable [LE α] [LT α]

@[refl]
public theorem le_refl [IsPreorder α] (a: α) : a ≤ a := refl _
public theorem le_trans [IsPreorder α] {a b c: α} : a ≤ b -> b ≤ c -> a ≤ c := htrans
public theorem le_antisymm [IsPartialOrder α] {a b: α} : a ≤ b -> b ≤ a -> a = b := antisymm _ _
public theorem lt_connected [IsLinearOrder α] (a b: α) : a < b ∨ a = b ∨ b < a := connected _ _

public theorem le_of_lt [IsLawfulLT α] {a b: α} (h: a < b) : a ≤ b := (lt_iff_le_and_not_ge.mp h).left
public theorem not_ge_of_lt [IsLawfulLT α] {a b: α} (h: a < b) : ¬b ≤ a := (lt_iff_le_and_not_ge.mp h).right
public theorem le_of_eq [IsPreorder α] {a b: α} (h: a = b) : a ≤ b := h ▸ le_refl a
public theorem ne_of_lt [IsPreorder α] {a b: α} (h: a < b) : a ≠ b := by intro rfl; exact not_ge_of_lt h (le_refl _)
public theorem ne_of_gt [IsPreorder α] {a b: α} (h: a < b) : b ≠ a := by intro rfl; exact not_ge_of_lt h (le_refl _)

end Property

section Opposite

variable [LE α] [LT α] [Max α] [Min α]

public instance [IsLawfulLT α] : IsLawfulLT αᵒᵖ where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := α)

public instance [IsPreorder α] : IsPreorder αᵒᵖ where
  refl a := le_refl a.get
  htrans h g := le_trans (α := α) g h

public instance [IsPartialOrder α] : IsPartialOrder αᵒᵖ where
  antisymm {_ _} h g := le_antisymm (α := α) g h

public instance [IsLinearOrder α] : IsLinearOrder αᵒᵖ where
  connected a b := by
    rcases lt_connected b.get a.get with h | rfl | h
    left; assumption
    right; left; rfl
    right; right; assumption

public instance [IsLawfulMax α] : IsLawfulMin αᵒᵖ where
  min_le_left := left_le_max (α := α)
  min_le_right := right_le_max (α := α)
public instance [IsLawfulMin α] : IsLawfulMax αᵒᵖ where
  left_le_max := min_le_left (α := α)
  right_le_max := min_le_right (α := α)

public instance [IsSupSemilattice α] : IsInfSemilattice αᵒᵖ where
  le_min := max_le (α := α)
public instance [IsInfSemilattice α] : IsSupSemilattice αᵒᵖ where
  max_le := le_min (α := α)

public instance [IsLattice α] : IsLattice αᵒᵖ where

end Opposite

section Theorems

variable [LE α] [LT α]

public theorem le_total [IsLinearOrder α] (a b: α) : a ≤ b ∨ b ≤ a := by
  rcases lt_connected a b with h | rfl | h
  left; apply le_of_lt; assumption
  left; apply le_refl
  right; apply le_of_lt; assumption

public instance [IsLinearOrder α] (a b: α) : ExcludedMiddle (a ≤ b) where
  excluded_middle := by
    rcases lt_connected a b with h | h | h
    left; apply le_of_lt; assumption
    left; apply le_of_eq; assumption
    right; intro g
    exact (lt_iff_le_and_not_ge.mp h).right g

public instance [IsLinearOrder α] (a b: α) : ExcludedMiddle (a < b) where
  excluded_middle := by
    rcases em (a ≤ b ∧ ¬(b ≤ a)) with h | h
    · left; apply lt_iff_le_and_not_ge.mpr; assumption
    · right; intro g; apply h; apply lt_iff_le_and_not_ge.mp; assumption

public theorem lt_of_lt_of_le [IsPreorder α] {a b c: α} (h: a ≤ b) (g: b < c) : a < c := by
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  apply le_trans h (le_of_lt g)
  intro h'
  exact not_ge_of_lt g (le_trans h' h)

public theorem lt_of_le_of_lt [IsPreorder α] {a b c: α} (h: a < b) (g: b ≤ c) : a < c := by
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  apply le_trans (le_of_lt h) g
  intro h'
  exact not_ge_of_lt h (le_trans g h')

public theorem lt_trans [IsPreorder α] {a b c: α} (h: a < b) (g: b < c) : a < c := by
  apply lt_iff_le_and_not_ge.mpr
  replace ⟨h₀, h₁⟩ := lt_iff_le_and_not_ge.mp h
  replace ⟨g₀, g₁⟩ := lt_iff_le_and_not_ge.mp g
  apply And.intro
  apply le_trans <;> assumption
  intro h
  exact g₁ (le_trans h h₀)

public theorem lt_or_eq_of_le [ExcludedMiddleLE α] [IsPartialOrder α] {a b: α} (h: a ≤ b) : a < b ∨ a = b := by
  rcases em (b ≤ a) with g | g
  right; apply le_antisymm <;> assumption
  left; apply lt_iff_le_and_not_ge.mpr; apply And.intro <;> assumption

public theorem lt_of_not_ge [IsLinearOrder α] {a b: α} (h: ¬b ≤ a) : a < b := by
  rcases le_total a b
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro <;> assumption
  contradiction

public theorem le_of_not_gt [IsLinearOrder α] {a b: α} (h: ¬b < a) : a ≤ b := by
  apply LEM.byContradiction
  intro g; apply h; apply lt_of_not_ge
  assumption

public theorem le_or_gt [IsLinearOrder α] (a b: α) : a ≤ b ∨ b < a := by
  rcases lt_connected a b with h | rfl | h
  left; exact le_of_lt h; left; rfl
  right; assumption

public theorem of_le_bot [IsPartialOrder α] [Bot α] [IsLawfulBot α] {a: α} (h: a ≤ ⊥) : a = ⊥ :=
  le_antisymm h (bot_le _)
public theorem of_top_le [IsPartialOrder α] [Top α] [IsLawfulTop α] {a: α} (h: ⊤ ≤ a) : a = ⊤ :=
  le_antisymm (le_top _) h


section Max

variable [Max α] [IsSupSemilattice α]

public theorem max_comm (a b: α) : a ⊔ b = b ⊔ a := by
  apply le_antisymm
  iterate 2
  apply max_le; apply right_le_max; apply left_le_max

public theorem max_assoc (a b c: α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  repeat any_goals apply max_le
  apply left_le_max
  apply le_trans _ (right_le_max _ _)
  apply left_le_max
  apply le_trans _ (right_le_max _ _)
  apply right_le_max
  apply le_trans _ (left_le_max _ _)
  apply left_le_max
  apply le_trans _ (left_le_max _ _)
  apply right_le_max
  apply right_le_max

public theorem max_eq_left {a b: α} (h: b ≤ a) : a ⊔ b = a := by
  apply le_antisymm
  apply max_le; rfl; assumption
  apply left_le_max

public theorem max_eq_right {a b: α} (h: a ≤ b) : a ⊔ b = b := by
  apply le_antisymm
  apply max_le; assumption; rfl
  apply right_le_max

variable [IsLinearOrder α]

public theorem max_eq (a b: α) : a ⊔ b = a ∨ a ⊔ b = b := by
  rcases le_total a b with h | h
  right; exact max_eq_right h
  left; exact max_eq_left h

public theorem of_lt_max {k a b: α} (h: k < a ⊔ b) : k < a ∨ k < b := by
  rcases le_or_gt a k with ga | g
  rcases le_or_gt b k with gb | g
  · nomatch not_ge_of_lt h (max_le ga gb)
  · right; assumption
  · left; assumption

end Max

section Min

variable [Min α] [IsInfSemilattice α]

public theorem min_comm (a b: α) : a ⊓ b = b ⊓ a :=
  max_comm (α := αᵒᵖ) _ _

public theorem min_assoc (a b c: α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  max_assoc (α := αᵒᵖ) _ _ _

public theorem min_eq_left {a b: α} (h: a ≤ b) : a ⊓ b = a :=
  max_eq_left (α := αᵒᵖ) h

public theorem min_eq_right {a b: α} (h: b ≤ a) : a ⊓ b = b :=
  max_eq_right (α := αᵒᵖ) h

variable [IsLinearOrder α]

public theorem min_eq (a b: α) : a ⊓ b = a ∨ a ⊓ b = b :=
  max_eq (α := αᵒᵖ) _ _

public theorem of_min_lt {k a b: α} (h: a ⊓ b < k) : a < k ∨ b < k :=
  of_lt_max (α := αᵒᵖ) h

end Min

end Theorems

instance : IsLinearOrder ℕ where
  lt_iff_le_and_not_ge := Nat.lt_iff_le_and_not_ge
  refl := Nat.le_refl
  htrans := Nat.le_trans
  antisymm _ _ := Nat.le_antisymm
  connected := Nat.lt_trichotomy
instance : IsLattice ℕ where
  left_le_max := Nat.le_max_left
  right_le_max := Nat.le_max_right
  min_le_left := Nat.min_le_left
  min_le_right := Nat.min_le_right
  max_le h g := Nat.max_le.mpr ⟨h, g⟩
  le_min h g := Nat.le_min.mpr ⟨h, g⟩

instance : IsLinearOrder ℤ where
  lt_iff_le_and_not_ge := Int.lt_iff_le_and_not_ge
  refl := Int.le_refl
  htrans := Int.le_trans
  antisymm _ _ := Int.le_antisymm
  connected := Int.lt_trichotomy
instance : IsLattice ℤ where
  left_le_max := Int.le_max_left
  right_le_max := Int.le_max_right
  min_le_left := Int.min_le_left
  min_le_right := Int.min_le_right
  max_le h g := Int.max_le.mpr ⟨h, g⟩
  le_min h g := Int.le_min.mpr ⟨h, g⟩

section Hom

public abbrev OrderHom (α β: Type*) [LE α] [LE β] := (· ≤ ·: α -> α -> Prop) →r (· ≤ ·: β -> β -> Prop)
public abbrev OrderEmbedding (α β: Type*) [LE α] [LE β] := (· ≤ ·: α -> α -> Prop) ↪r (· ≤ ·: β -> β -> Prop)
public abbrev OrderEquiv (α β: Type*) [LE α] [LE β] := (· ≤ ·: α -> α -> Prop) ≃r (· ≤ ·: β -> β -> Prop)

infixr:80 " →o " => OrderHom
infixr:80 " ↪o " => OrderEmbedding
infixr:80 " ≃o " => OrderEquiv

public instance
  [LE α] [LT α] [IsPartialOrder α]
  [LE β] [LT β] [IsPreorder β] : EmbeddingLike (α →o β) α β where
  coeInjective f a b h := by
    apply le_antisymm
    apply map_rel_rev f
    rw [h]
    apply map_rel_rev f
    rw [h]

end Hom

@[expose] public def Setoid.preorder (α: Type*) [LE α] [LT α] [IsPreorder α] : Setoid α where
  r a b := a ≤ b ∧ b ≤ a
  iseqv := {
    refl _ := ⟨le_refl _, le_refl _⟩
    symm := And.symm,
    trans h g := ⟨le_trans h.left g.left, le_trans g.right h.right⟩
  }
