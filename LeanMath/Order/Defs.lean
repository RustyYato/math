import LeanMath.Logic.Relation.Defs

open Relation

class IsLawfulLT (α: Type) [LE α] [LT α] : Prop where
  protected lt_iff_le_and_not_ge {a b: α} : a < b ↔ a ≤ b ∧ ¬b ≤ a

class IsPreorder (α: Type) [LE α] [LT α] : Prop
  extends IsLawfulLT α, @Relation.IsRefl α (· ≤ ·), @Relation.IsTrans α (· ≤ ·) where

class IsPartialOrder (α: Type) [LE α] [LT α] : Prop
  extends IsPreorder α, Relation.IsAntisymm (α := α) (· ≤ ·) (· = ·) where

class IsLinearOrder (α: Type) [LE α] [LT α] : Prop
  extends IsPartialOrder α, @Relation.IsTotal α (· ≤ ·) where

variable [LE α] [LT α]

section

variable [IsLawfulLT α] {a b c: α}

def lt_iff_le_and_not_ge : a < b ↔ a ≤ b ∧ ¬b ≤ a := IsLawfulLT.lt_iff_le_and_not_ge

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

variable [DecidableRel (α := α) (· ≤ ·)]

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

end
