import LeanMath.Order.Filter.Defs

/-- a limit is a non-trivial filter -/
structure Limit (α: Type*) extends Order.Filter (Set α) where
  ne_bot: toFilter ≠ ⊥

namespace Limit

attribute [coe] Limit.toFilter

instance : Coe (Limit α) (Order.Filter (Set α)) where
  coe l := l.toFilter

instance : Membership (Set α) (Limit α) where
  mem l s := s ∈ l.toFilter

instance : IsFilter (Limit α) (Set α) where

def Eventually (P: α -> Prop) (f: Limit α) : Prop := Set.ofMem P ∈ f
def Frequently (P: α -> Prop) (f: Limit α) : Prop := ¬f.Eventually fun x => ¬P x

def Eventually.Frequently {P: α -> Prop} {f: Limit α} (h: f.Eventually P) : f.Frequently P := by
  intro g
  replace h : Set.ofMem P ∈ f := h
  replace g : (Set.ofMem P)ᶜ ∈ f := g
  apply f.ne_bot
  rw [Order.Filter.eq_bot_iff_mem_bot]
  show ⊥ ∈ f
  rw [show (⊥: Set α) = Set.ofMem P ∩ (Set.ofMem P)ᶜ from ?_]
  apply mem_min
  assumption
  assumption
  ext x; simp

def Frequently.exists [LEM] {P : α → Prop} {f : Limit α} (hp : Frequently P f) : ∃ x, P x := by
  rw [←LEM.not_not (P := ∃x, P x), not_exists]
  intro h; apply hp; clear hp
  show Set.ofMem (¬P ·) ∈ f
  rw [show Set.ofMem (¬P ·) = ⊤ from ?_]
  apply Order.Filter.top_mem
  ext; simp; apply h

end Limit
