import LeanMath.Logic.Relation.Defs
import LeanMath.Data.TopBot.Defs
import LeanMath.Data.OfEquiv.Defs

open Relation

abbrev OrderHom (α β: Type*) [LE α] [LE β] := (· ≤ ·: α -> α -> Prop) →r (· ≤ ·: β -> β -> Prop)
abbrev OrderEmbedding (α β: Type*) [LE α] [LE β] := (· ≤ ·: α -> α -> Prop) ↪r (· ≤ ·: β -> β -> Prop)
abbrev OrderEquiv (α β: Type*) [LE α] [LE β] := (· ≤ ·: α -> α -> Prop) ≃r (· ≤ ·: β -> β -> Prop)

abbrev IsOrderHom (F α β: Type*) [FunLike F α β] [LE α] [LE β] :=  IsRelHom F (α := α) (β := β) (· ≤ ·) (· ≤ ·)

infixr:50 " →o " => OrderHom
infixr:50 " ↪o " => OrderEmbedding
infixr:50 " ≃o " => OrderEquiv

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

abbrev IsLETotal (α: Type*) [LE α] := @Relation.IsTotal α (· ≤ ·)
abbrev IsLTTrichotomous (α: Type*) [LT α] := @Relation.IsTrichotomous α (· < ·) (· = ·)

class IsLinearOrder (α: Type*) [LE α] [LT α] : Prop
  extends IsPartialOrder α, IsLTTrichotomous α where

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

class LemLE (α: Type*) [LE α] where
  protected le_or_not_le (a b: α) : a ≤ b ∨ ¬a ≤ b

def le_or_not_le [LE α] [LemLE α] (a b: α) : a ≤ b ∨ ¬a ≤ b := LemLE.le_or_not_le _ _

instance [LE α] [∀a b: α, ExcludedMiddle (a ≤ b)] : LemLE α where
  le_or_not_le a b := by
    rcases em (a ≤ b)
    left; assumption
    right; assumption

variable [LE α] [LT α] [Min α] [Max α] [Top α] [Bot α]
  [LE β] [LT β]

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

def map_le [FunLike F α β] [IsOrderHom F α β] (f: F) (a b: α) : a ≤ b ↔ f a ≤ f b := by
  apply map_rel

def map_lt [FunLike F α β] [IsOrderHom F α β] [IsLawfulLT α] [IsLawfulLT β] (f: F) (a b: α) : a < b ↔ f a < f b := by
  rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, map_le f, map_le f]

def toLtHom [FunLike F α β] [IsOrderHom F α β] [IsLawfulLT β] (f: F) : (· < ·: α -> α -> Prop) →r (· < ·: β -> β -> Prop) where
  toFun := f
  map_rel := map_lt f _ _

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

instance [@Relation.IsRefl α (· ≤ ·)] : @Relation.IsIrrefl α (· < ·) where
  irrefl h := (not_le_of_lt h) (Relation.refl _)

instance (priority := 900) [@Relation.IsRefl α (· ≤ ·)] [IsLTTrichotomous α] : IsLETotal α where
  total a b := by
    rcases trichotomous (· < ·) a b with h | rfl | h
    · left; apply le_of_lt
      assumption
    · left; rfl
    · right; apply le_of_lt
      assumption

instance (priority := 900) [LemLE α] [@Relation.IsAntisymm α (· ≤ ·) (· = ·)] [IsLETotal α] : IsLTTrichotomous α where
  trichotomous a b := by
    rcases total (· ≤ ·) a b with g | g
    rcases le_or_not_le b a with h | h
    · right; left
      exact antisymm g h
    · left; apply lt_iff_le_and_not_ge.mpr
      apply And.intro <;> assumption
    rcases le_or_not_le a b with h | h
    · right; left
      exact antisymm h g
    · right; right; apply lt_iff_le_and_not_ge.mpr
      apply And.intro <;> assumption

instance : IsLinearOrder Nat where
  lt_iff_le_and_not_ge := Nat.lt_iff_le_and_not_ge
  refl := Nat.le_refl
  trans := Nat.le_trans
  antisymm := Nat.le_antisymm
  trichotomous := Nat.lt_trichotomy

instance : IsLinearOrder Int where
  lt_iff_le_and_not_ge := Int.lt_iff_le_and_not_ge
  refl := Int.le_refl
  trans := Int.le_trans
  antisymm := Int.le_antisymm
  trichotomous := Int.lt_trichotomy

instance : IsLinearOrder Bool where
  lt_iff_le_and_not_ge := by decide
  refl := by decide
  trans := by decide
  antisymm := by decide
  trichotomous := by decide

instance : IsLattice Bool where
  left_le_max := by decide
  right_le_max := by decide
  max_le := by decide
  min_le_left := by decide
  min_le_right := by decide
  le_min := by decide

instance : @Relation.IsWelFounded Bool (· < ·) where
  wf := by
    apply WellFounded.intro
    intro a; apply Acc.intro
    intro b h
    have : a = true ∧ b = false := by decide +revert
    obtain ⟨rfl, rfl⟩ := this
    apply Acc.intro
    nofun

instance : LE PEmpty where
  le := nofun
instance : LT PEmpty where
  lt := nofun
instance : Min PEmpty where
  min := nofun
instance : Max PEmpty where
  max := nofun

instance : IsLinearOrder PEmpty where
  lt_iff_le_and_not_ge := nofun
  refl := nofun
  trans := nofun
  antisymm := nofun
  trichotomous := nofun

instance : IsLattice PEmpty where
  left_le_max := nofun
  right_le_max := nofun
  max_le := nofun
  min_le_left := nofun
  min_le_right := nofun
  le_min := nofun

instance : @Relation.IsWelFounded PEmpty r where
  wf := by
    apply WellFounded.intro
    nofun

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

-- variable [DecidableLE α]

def le_refl [IsPreorder α] (a: α) : a ≤ a := Relation.refl _
def le_of_eq [IsPreorder α] {a b: α} : a = b -> a ≤ b := fun h => h ▸ le_refl _

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
def lt_of_le_of_ne [IsPartialOrder α] {a b: α} (h: a ≤ b) (g: a ≠ b) : a < b := by
  apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  assumption
  intro h'
  exact g (Relation.antisymm h h')

def ne_of_lt [IsPreorder α] {a b: α} : a < b -> a ≠ b := by
  rintro h rfl
  exact Relation.irrefl h
def ne_of_gt [IsPreorder α] {a b: α} : a > b -> a ≠ b := Ne.symm ∘ ne_of_lt

def lt_or_eq_of_le [LemLE α] [IsPartialOrder α] {a b: α} (h: a ≤ b) : a < b ∨ a = b := by
  rcases le_or_not_le b a with g | g
  right; exact antisymm h g
  left; apply lt_iff_le_and_not_ge.mpr
  apply And.intro
  assumption
  assumption

instance [IsPreorder α] : @Relation.IsTrans α (· < ·) where
  trans h g := lt_of_lt_of_le h (le_of_lt g)

def le_total [IsLinearOrder α] (a b: α) : a ≤ b ∨ b ≤ a := total (· ≤ ·) a b
def lt_trichotomy [IsLTTrichotomous α] (a b: α) : a < b ∨ a = b ∨ b < a := trichotomous (· < ·) a b

def lt_trans [IsPreorder α] {a b c: α} : a < b -> b < c -> a < c := Relation.trans
def le_antisymm [IsPartialOrder α] {a b: α} : a ≤ b -> b ≤ a -> a = b := Relation.antisymm

instance [LE α] [LT α] [IsLinearOrder α] : LemLE α where
  le_or_not_le a b := by
    rcases lt_trichotomy a b with h | rfl | h
    left; apply le_of_lt; assumption
    left; rfl
    right
    exact not_le_of_lt h

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

def not_lt [IsLinearOrder α] {a b: α} : ¬a < b ↔ b ≤ a := by
  apply Iff.intro
  apply le_of_not_lt
  intro h g
  exact Relation.irrefl (lt_of_le_of_lt h g)

def not_le [IsLinearOrder α] {a b: α} : ¬a ≤ b ↔ b < a := by
  apply Iff.intro
  · intro h
    cases Relation.total (α := α) (· ≤ ·) b a
    apply lt_iff_le_and_not_ge.mpr
    apply And.intro <;> assumption
    contradiction
  intro h g
  exact Relation.irrefl (lt_of_le_of_lt g h)

def min_eq [IsLinearOrder α] [IsLattice α] (a b: α) : a ⊓ b = a ∨ a ⊓ b = b := by
  rcases le_total a b with h | h
  left; apply le_antisymm
  apply min_le_left; apply le_min
  rfl; assumption
  right; apply le_antisymm
  apply min_le_right; apply le_min
  assumption; rfl

def max_eq [IsLinearOrder α] [IsLattice α] (a b: α) : a ⊔ b = a ∨ a ⊔ b = b := by
  rcases le_total a b with h | h
  right; apply le_antisymm
  apply max_le; assumption; rfl
  apply right_le_max
  left; apply le_antisymm
  apply max_le; rfl; assumption
  apply left_le_max

def max_eq_left [IsSemiLatticeMax α] {a b: α} (h: b ≤ a) : a ⊔ b = a := by
  apply le_antisymm
  apply max_le; rfl
  assumption
  apply left_le_max

def max_eq_right [IsSemiLatticeMax α] {a b: α} (h: a ≤ b) : a ⊔ b = b := by
  apply le_antisymm
  apply max_le
  assumption; rfl
  apply right_le_max

def min_eq_left [IsSemiLatticeMin α] {a b: α} (h: a ≤ b) : a ⊓ b = a :=
  max_eq_left (α := αᵒᵖ) h

def min_eq_right [IsSemiLatticeMin α] {a b: α} (h: b ≤ a) : a ⊓ b = b :=
  max_eq_right (α := αᵒᵖ) h

def le_or_lt [IsLinearOrder α] (a b: α) : a ≤ b ∨ b < a := by
  rcases Relation.trichotomous (α := α) (· < ·) a b with h | h | h
  left; apply le_of_lt; assumption
  left; rw [h]
  right; assumption

def lt_or_le [IsLinearOrder α] (a b: α) : a < b ∨ b ≤ a := by
  rcases Relation.trichotomous (α := α) (· < ·) a b with h | h | h
  left; assumption
  right; rw [h]
  right; apply le_of_lt; assumption

def of_lt_max [IsLinearOrder α] [IsSemiLatticeMax α] {x a b: α} : x < a ⊔ b -> x < a ∨ x < b := by
  intro h
  rcases le_or_not_le a x with ha | ha
  rcases le_or_not_le b x with hb | hb
  · nomatch not_le_of_lt h (max_le ha hb)
  · right
    apply not_le.mp
    assumption
  · left
    apply not_le.mp
    assumption

def lt_min [IsLinearOrder α] [IsSemiLatticeMin α] {x a b: α} : x < a -> x < b -> x < a ⊓ b := by
  intro ha hb
  rcases le_total a b with h | h
  rwa [min_eq_left h]
  rwa [min_eq_right h]

end

instance [DecidableLE α] [FunLike F α β] [IsOrderHom F α β] [IsPartialOrder α] [IsPreorder β] : EmbeddingLike F α β where
  coeEmbedding f := {
    toFun := f
    inj := by
      intro a b g
      have : a ≤ b := by rw [map_le f, g]
      have : b ≤ a := by rw [map_le f, g]
      apply le_antisymm <;> assumption
  }
  coeInj := by
    intro a b h
    dsimp at h
    exact DFunLike.coeInj (Embedding.mk.inj h)

def OrderEmbedding.subtype_val {P: α -> Prop} : Subtype P ↪o α where
  toEmbedding := Embedding.subtype_val
  map_rel := Iff.rfl

def RelEmbedding.subtype_val {P: α -> Prop} : (· < ·: Subtype P -> Subtype P -> Prop) ↪r (· < ·: α -> α -> Prop) where
  toEmbedding := Embedding.subtype_val
  map_rel := Iff.rfl

instance [IsLawfulLT α] {P: α -> Prop} : IsLawfulLT (Subtype P) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := α)
instance [IsPreorder α] {P: α -> Prop} : IsPreorder (Subtype P) where
  refl _ := le_refl (α := α) _
  trans := le_trans (α := α)
instance [IsPartialOrder α] {P: α -> Prop} : IsPartialOrder (Subtype P) where
  antisymm h g := Subtype.ext (le_antisymm h g)
instance [IsLinearOrder α] {P: α -> Prop} : IsLinearOrder (Subtype P) where
  trichotomous a b := by
    rcases Relation.trichotomous (α := α) (· < ·) a.val b.val with h | h | h
    · left; assumption
    · right; left; ext; assumption
    · right; right; assumption

instance [@Relation.IsWellOrder α (· < ·)] {P: α -> Prop} : Relation.IsWelFounded (α := Subtype P) (· < ·) :=
  RelEmbedding.subtype_val.liftWellfounded

instance [@Relation.IsTotal α (· ≤ ·)] {P: α -> Prop} : Relation.IsTotal (α := Subtype P) (· ≤ ·) :=
  OrderEmbedding.subtype_val.liftTotal

def order_emb_of_map_rel
  [LE α] [LT α] [IsPreorder α] [Relation.IsTrichotomous (α := α) (· < ·) (· = ·)]
  [LE β] [LT β] [IsPreorder β] [Relation.IsTrichotomous (α := β) (· < ·) (· = ·)]
  (f: α -> β) (h: ∀x y: α, x ≤ y ↔ f x ≤ f y) : α ↪o β where
  toFun := f
  inj {a b} heq := by
    rcases lt_trichotomy a b with h₀ | h₀ | h₀
    · have : f a < f b := by rwa [lt_iff_le_and_not_ge, ←h, ←h, ←lt_iff_le_and_not_ge]
      rw [heq] at this; nomatch Relation.irrefl this
    · assumption
    · have : f b < f a := by rwa [lt_iff_le_and_not_ge, ←h, ←h, ←lt_iff_le_and_not_ge]
      rw [heq] at this; nomatch Relation.irrefl this
  map_rel := h _ _

def rel_emb_of_map_rel
  {r: α -> α -> Prop} {s: β -> β -> Prop}
  [Relation.IsTrichotomous r (· = ·)] [Relation.IsIrrefl r]
  [Relation.IsTrichotomous s (· = ·)] [Relation.IsIrrefl s]
  (f: α -> β) (h: ∀x y: α, r x y ↔ s (f x) (f y)) : r ↪r s where
  toFun := f
  inj {a b} heq := by
    rcases Relation.trichotomous r a b with h₀ | h₀ | h₀
    · have : s (f a) (f b) := by rwa [←h]
      rw [heq] at this; nomatch Relation.irrefl this
    · assumption
    · have : s (f b) (f a) := by rwa [←h]
      rw [heq] at this; nomatch Relation.irrefl this
  map_rel := h _ _

def toLtEmb
  [IsLinearOrder α] [IsLinearOrder β]
  [FunLike F α β] [IsOrderHom F α β] [IsLawfulLT β] (f: F) : (· < ·: α -> α -> Prop) ↪r (· < ·: β -> β -> Prop) :=
  rel_emb_of_map_rel f (map_lt f)

def toLtEquiv
  [IsLinearOrder α] [IsLinearOrder β]
  [EquivLike F α β] [IsOrderHom F α β] [IsLawfulLT β] (f: F) : (· < ·: α -> α -> Prop) ≃r (· < ·: β -> β -> Prop) where
  toEquiv := Equiv.coe f
  map_rel := map_rel (rel_emb_of_map_rel f (map_lt f))

namespace OfEquiv

variable (f: α ≃ β)

set_option allowUnsafeReducibility true in
attribute [local semireducible] OfEquiv

protected scoped instance [Top β] : Top (OfEquiv f) where
  top := f.symm ⊤
protected scoped instance [Bot β] : Bot (OfEquiv f) where
  bot := f.symm ⊥

@[simp] def top_def [Top β] : (⊤: OfEquiv f) = f.symm ⊤ := rfl
@[simp] def bot_def [Bot β] : (⊥: OfEquiv f) = f.symm ⊥ := rfl

protected scoped instance [IsLawfulLT β] : IsLawfulLT (OfEquiv f) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := β)
protected scoped instance [IsPreorder β] : IsPreorder (OfEquiv f) where
  refl _ := le_refl (α := β) _
  trans := le_trans (α := β)
protected scoped instance [IsPartialOrder β] : IsPartialOrder (OfEquiv f) where
  antisymm h g := inj f (le_antisymm h g)
protected scoped instance [IsLTTrichotomous β] : IsLTTrichotomous (OfEquiv f) :=
  inferInstanceAs (Relation.IsTrichotomous (pullback_rel (· < ·) f) (· = ·))
protected scoped instance [IsLinearOrder β] : IsLinearOrder (OfEquiv f) where

protected scoped instance [Min β] [IsLawfulMin β] : IsLawfulMin (OfEquiv f) where
  min_le_left {a b} := by dsimp; rw [Equiv.symm_coe]; apply min_le_left
  min_le_right {a b} := by dsimp; rw [Equiv.symm_coe]; apply min_le_right

protected scoped instance [Max β] [IsLawfulMax β] : IsLawfulMax (OfEquiv f) where
  left_le_max {a b} := by dsimp; rw [Equiv.symm_coe]; apply left_le_max
  right_le_max {a b} := by dsimp; rw [Equiv.symm_coe]; apply right_le_max

protected scoped instance [Top β] [IsLawfulTop β] : IsLawfulTop (OfEquiv f) where
  le_top a := by dsimp; rw [Equiv.symm_coe]; apply le_top

protected scoped instance [Bot β] [IsLawfulBot β] : IsLawfulBot (OfEquiv f) where
  bot_le a := by dsimp; rw [Equiv.symm_coe]; apply bot_le

protected scoped instance [Min β] [IsSemiLatticeMin β] : IsSemiLatticeMin (OfEquiv f) where
  le_min {x a b} ha hb := by dsimp; rw [Equiv.symm_coe]; apply le_min <;> assumption
protected scoped instance [Max β] [IsSemiLatticeMax β] : IsSemiLatticeMax (OfEquiv f) where
  max_le {x a b} ha hb := by dsimp; rw [Equiv.symm_coe]; apply max_le <;> assumption
protected scoped instance [Max β] [Min β] [IsLattice β] : IsLattice (OfEquiv f) where

end OfEquiv
