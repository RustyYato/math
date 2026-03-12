import LeanMath.Logic.Relation.Defs
import LeanMath.Data.TopBot.Defs

open Relation

infixl:68 " ⊔ " => max
infixl:69 " ⊓ " => min

def OrderOpp (α: Sort u) := α

def OrderOpp.get : OrderOpp α ↪ α := Embedding.id _
def OrderOpp.mk : α ↪ OrderOpp α := Embedding.id _

postfix:max "ᵒᵖ" => OrderOpp

instance [LE α] : LE αᵒᵖ where
  le a b := b.get ≤ a.get

instance [LT α] : LT αᵒᵖ where
  lt a b := b.get < a.get

instance [Max α] : Min αᵒᵖ where
  min a b := .mk <| a.get ⊔ b.get
instance [Min α] : Max αᵒᵖ where
  max a b := .mk <| a.get ⊓ b.get

instance [Top α] : Bot αᵒᵖ where
  bot := .mk ⊤
instance [Bot α] : Top αᵒᵖ where
  top := .mk ⊥

class IsLawfulLT (α: Type*) [LE α] [LT α] : Prop where
  protected lt_iff_le_and_not_ge {a b: α} : a < b ↔ a ≤ b ∧ ¬b ≤ a

class IsPreorder (α: Type*) [LE α] [LT α] : Prop
  extends IsLawfulLT α, @Relation.IsRefl α (· ≤ ·), @Relation.IsTrans α (· ≤ ·) where

class IsPartialOrder (α: Type*) [LE α] [LT α] : Prop
  extends IsPreorder α, Relation.IsAntisymm (α := α) (· ≤ ·) (· = ·) where

class IsLinearOrder (α: Type*) [LE α] [LT α] : Prop
  extends IsPartialOrder α, @Relation.IsTotal α (· ≤ ·) where

class IsLawfulMax (α: Type*) [LE α] [Max α] : Prop where
  protected left_le_max {a b: α} : a ≤ a ⊔ b
  protected right_le_max {a b: α} : b ≤ a ⊔ b

class IsLawfulMin (α: Type*) [LE α] [Min α] : Prop where
  protected min_le_left {a b: α} : a ⊓ b ≤ a
  protected min_le_right {a b: α} : a ⊓ b ≤ b

class IsSemiLatticeMax (α: Type*) [LE α] [LT α] [Max α] : Prop extends IsPartialOrder α, IsLawfulMax α where
  protected max_le {x a b: α} : a ≤ x -> b ≤ x -> a ⊔ b ≤ x

class IsSemiLatticeMin (α: Type*) [LE α] [LT α] [Min α] : Prop extends IsPartialOrder α, IsLawfulMin α where
  protected le_min {x a b: α} : x ≤ a -> x ≤ b -> x ≤ a ⊓ b


class IsLattice (α: Type*) [LE α] [LT α] [Max α] [Min α] : Prop extends IsSemiLatticeMax α, IsSemiLatticeMin α where

variable [LE α] [LT α] [Min α] [Max α] [Top α] [Bot α]

def max_le [IsSemiLatticeMax α] {x a b: α} : a ≤ x -> b ≤ x -> a ⊔ b ≤ x :=
  IsSemiLatticeMax.max_le

def left_le_max [IsLawfulMax α] {a b: α} : a ≤ a ⊔ b :=
  IsLawfulMax.left_le_max
def right_le_max [IsLawfulMax α] {a b: α} : b ≤ a ⊔ b :=
  IsLawfulMax.right_le_max

def le_min [IsSemiLatticeMin α] {x a b: α} : x ≤ a -> x ≤ b -> x ≤ a ⊓ b :=
  IsSemiLatticeMin.le_min

def min_le_left [IsLawfulMin α] {a b: α} : a ⊓ b ≤ a :=
  IsLawfulMin.min_le_left
def min_le_right [IsLawfulMin α] {a b: α} : a ⊓ b ≤ b :=
  IsLawfulMin.min_le_right

section

variable [IsLawfulLT α] {a b c: α}

def lt_iff_le_and_not_ge : a < b ↔ a ≤ b ∧ ¬b ≤ a := IsLawfulLT.lt_iff_le_and_not_ge

instance : IsLawfulLT (αᵒᵖ) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := α)

instance [IsPreorder α] : IsPreorder (αᵒᵖ) where
  refl _ := Relation.refl (α := α) (R := (· ≤ ·)) _
  trans := flip <| Relation.trans (α := α) (R := (· ≤ ·))

instance [IsPartialOrder α] : IsPartialOrder (αᵒᵖ) where
  antisymm h g := OrderOpp.get.inj <| Relation.antisymm (α := α) (R := (· ≤ ·)) g h

instance [IsSemiLatticeMax α] : IsSemiLatticeMin (αᵒᵖ) where
  min_le_left := left_le_max (α := α)
  min_le_right := right_le_max (α := α)
  le_min := max_le (α := α)
instance [IsSemiLatticeMin α] : IsSemiLatticeMax (αᵒᵖ) where
  left_le_max := min_le_left (α := α)
  right_le_max := min_le_right (α := α)
  max_le := le_min (α := α)

instance [IsSemiLatticeMin α] : IsSemiLatticeMax (αᵒᵖ) where
  left_le_max := min_le_left (α := α)
  right_le_max := min_le_right (α := α)
  max_le := le_min (α := α)

instance [IsLawfulTop α] : IsLawfulBot αᵒᵖ where
  bot_le := le_top (α := α)

instance [IsLawfulBot α] : IsLawfulTop αᵒᵖ where
  le_top := bot_le (α := α)

def le_of_lt (h: a < b) : a ≤ b := (lt_iff_le_and_not_ge.mp h).left
def not_le_of_lt (h: a < b) : ¬b ≤ a := (lt_iff_le_and_not_ge.mp h).right

instance (priority := 900) [@Relation.IsRefl α (· ≤ ·)] [Relation.IsTrichotomous (α := α) (· < ·) (· = ·)] : @Relation.IsTotal α (· ≤ ·) where
  total a b := by
    rcases trichotomous (· < ·) a b with h | rfl | h
    · left; apply le_of_lt
      assumption
    · left; rfl
    · right; apply le_of_lt
      assumption

instance (priority := 900) [DecidableRel (α := α) (· ≤ ·)] [@Relation.IsAntisymm α (· ≤ ·) (· = ·)] [@Relation.IsTotal α (· ≤ ·)] : Relation.IsTrichotomous (α := α) (· < ·) (· = ·) where
  trichotomous a b := by
    rcases total (· ≤ ·) a b with g | g
    by_cases h:b ≤ a
    · right; left
      exact antisymm g h
    · left; apply lt_iff_le_and_not_ge.mpr
      apply And.intro <;> assumption
    by_cases h:a ≤ b
    · right; left
      exact antisymm h g
    · right; right; apply lt_iff_le_and_not_ge.mpr
      apply And.intro <;> assumption

instance : IsLinearOrder Nat where
  lt_iff_le_and_not_ge := Nat.lt_iff_le_and_not_ge
  refl := Nat.le_refl
  trans := Nat.le_trans
  antisymm := Nat.le_antisymm
  total := Nat.le_total

instance : IsLinearOrder Int where
  lt_iff_le_and_not_ge := Int.lt_iff_le_not_le
  refl := Int.le_refl
  trans := Int.le_trans
  antisymm := Int.le_antisymm
  total := Int.le_total

instance : IsLattice Nat where
  left_le_max := Nat.le_max_left _ _
  right_le_max := Nat.le_max_right _ _
  max_le h g := Nat.max_le.mpr ⟨h, g⟩
  min_le_left := Nat.min_le_left _ _
  min_le_right := Nat.min_le_right _ _
  le_min h g := Nat.le_min.mpr ⟨h, g⟩

instance : IsLattice Int where
  left_le_max := Int.le_max_left _ _
  right_le_max := Int.le_max_right _ _
  max_le h g := Int.max_le.mpr ⟨h, g⟩
  min_le_left := Int.min_le_left _ _
  min_le_right := Int.min_le_right _ _
  le_min h g := Int.le_min.mpr ⟨h, g⟩

variable [DecidableRel (α := α) (· ≤ ·)]

def le_trans [IsPreorder α] {a b c: α} : a ≤ b -> b ≤ c -> a ≤ c := Relation.trans

def lt_of_lt_of_le [IsPreorder α] {a b c: α} (h: a < b) (g: b ≤ c) : a < c := by
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  · apply Relation.trans _ g
    apply le_of_lt
    assumption
  · intro g'
    replace ⟨h, h'⟩ := lt_iff_le_and_not_ge.mp h
    apply h'
    apply Relation.trans
    assumption
    assumption
def lt_of_le_of_lt [IsPreorder α] {a b c: α} (h: a ≤ b) (g: b < c) : a < c := by
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  · apply Relation.trans h
    apply le_of_lt
    assumption
  · intro h'
    replace ⟨g, g'⟩ := lt_iff_le_and_not_ge.mp g
    apply g'
    apply Relation.trans
    assumption
    assumption

def lt_or_eq_of_le [IsPartialOrder α] {a b: α} (h: a ≤ b) : a < b ∨ a = b := by
  by_cases g:b ≤ a
  right; exact antisymm h g
  left; apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  assumption
  assumption

instance [IsPreorder α] : @Relation.IsTrans α (· < ·) where
  trans h g := lt_of_lt_of_le h (le_of_lt g)

def le_total [IsLinearOrder α] (a b: α) : a ≤ b ∨ b ≤ a := total (· ≤ ·) a b
def lt_trichotomy [IsLinearOrder α] (a b: α) : a < b ∨ a = b ∨ b < a := trichotomous (· < ·) a b

def lt_trans [IsPreorder α] {a b c: α} : a < b -> b < c -> a < c := Relation.trans
def le_antisymm [IsPartialOrder α] {a b: α} : a ≤ b -> b ≤ a -> a = b := Relation.antisymm

def min_comm [IsSemiLatticeMin α] (a b: α) : a ⊓ b = b ⊓ a := by
  apply le_antisymm
  · apply le_min
    apply min_le_right
    apply min_le_left
  · apply le_min
    apply min_le_right
    apply min_le_left

def max_comm [IsSemiLatticeMax α] (a b: α) : a ⊔ b = b ⊔ a :=
  min_comm (α := αᵒᵖ) _ _

def max_assoc [IsSemiLatticeMax α] (a b c: α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  apply max_le
  apply max_le
  apply left_le_max
  apply le_trans left_le_max
  apply right_le_max
  apply le_trans right_le_max
  apply right_le_max
  apply max_le
  apply le_trans left_le_max
  apply left_le_max
  apply max_le
  apply le_trans right_le_max
  apply left_le_max
  apply right_le_max

def min_assoc [IsSemiLatticeMin α] (a b c: α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
  max_assoc (α := αᵒᵖ) _ _ _

def le_of_not_lt [IsLinearOrder α] {a b: α} : ¬b < a -> a ≤ b := by
  intro h
  rcases Relation.trichotomous (α := α) (· < ·) a b with _ | rfl | _
  apply le_of_lt
  assumption
  rfl
  contradiction

end
