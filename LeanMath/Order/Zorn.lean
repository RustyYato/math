import LeanMath.Order.Chain
import LeanMath.Order.Set

namespace Zorn

variable {α β : Type*} {r : α → α → Prop} {c : Set α} [Relation.IsTrans r]

def exists_maximal_of_chains_bounded (h : ∀ c, Set.IsChain r c → ∃ ub, ∀ a ∈ c, r a ub)
  (trans: ∀{a b c}, r a b -> r b c -> r a c := by exact Relation.trans):
  ∃ m, ∀ a, r m a → r a m := by
  have : ∃ ub, ∀ a ∈ Set.maxChain r, r a ub := h _ Set.maxChain_spec.left
  obtain ⟨ub, spec⟩ := this
  exists ub
  intro x rx
  apply spec
  suffices Set.maxChain r = insert x (Set.maxChain r) by
    rw [this]
    apply Set.mem_insert.mpr; left; rfl
  apply Set.maxChain_spec.right _ _
  intro y mem
  apply Set.mem_insert.mpr
  right; assumption
  apply (Set.IsChain.insert Set.maxChain_spec.left x)
  intro y mem
  right; right
  exact trans (spec _ mem) rx

variable [LE α] [LT α]

def preorder [IsPreorder α] (h : ∀ c : Set α, Set.IsChain (· ≤ ·) c → Set.BoundedAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a ≤ m := exists_maximal_of_chains_bounded <| by
    intro c hc
    have ⟨ub, hub⟩  := h c hc
    exists ub

def partialorder [IsPartialOrder α] (h : ∀ c : Set α, Set.IsChain (· ≤ ·) c → Set.BoundedAbove c) :
    ∃ m : α, ∀ a, m ≤ a → a = m := by
    have ⟨m, h⟩ := preorder h
    exists m; intro a g
    apply le_antisymm
    apply h
    assumption
    assumption

def preorder_in [IsPreorder α] (U: Set α) (h : ∀c ⊆ U, Set.IsChain (· ≤ ·) c → ∃ub ∈ U, ∀x ∈ c, x ≤ ub) :
    ∃ m ∈ U, ∀a ∈ U, m ≤ a → a ≤ m := by
    have ⟨m, spec⟩  := exists_maximal_of_chains_bounded (α := U) (r := fun x y => (x.val ≤ y.val)) ?_ ?_
    refine ⟨_, m.property, ?_⟩
    intro a mem sub
    apply spec ⟨_, mem⟩ sub
    intro s c
    obtain h := h (s.image Subtype.val) (by
      intro s' ⟨_, eq, _⟩
      subst s'
      apply Subtype.property) (by
        refine ⟨?_⟩
        intro ⟨_, a, mema, eqa⟩ ⟨_, b, memb, eqb⟩
        subst eqa; subst eqb
        unfold Set.Induced
        dsimp
        rcases c.trichotomous ⟨_, mema⟩ ⟨_, memb⟩ with lt | eq | gt
        left; assumption
        right; left
        cases eq; congr
        right; right; assumption)
    obtain ⟨ub, ub_in_S, h⟩ := h
    dsimp
    exists ⟨ub, ub_in_S⟩
    intro a mem
    dsimp
    apply h
    apply Set.mem_image'
    assumption
    intro a b c
    apply Relation.trans

def partialorder_in [IsPartialOrder α] (U: Set α) (h : ∀c ⊆ U, Set.IsChain (· ≤ ·) c → ∃ub ∈ U, ∀x ∈ c, x ≤ ub) :
    ∃ m ∈ U, ∀a ∈ U, m ≤ a → a = m := by
    have ⟨m, mem, h⟩ := preorder_in U h
    refine ⟨_, mem, ?_⟩
    intro a g _
    apply le_antisymm
    apply h
    assumption
    assumption
    assumption

end Zorn
