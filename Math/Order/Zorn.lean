module

public import Math.Order.Chain

namespace Math

variable {α β: Type*} {r: α -> α -> Prop} {c: Set α} [IsTrans r]

theorem exists_maximal_of_bounded_chains (h: ∀c, Set.IsChain r c -> ∃ub, ∀a ∈ c, r a ub) : ∃m, ∀a, r m a -> r a m := by
  have ⟨ub, spec⟩ : ∃ub, ∀a ∈ Set.maxChain r, r a ub := h _ Set.maxChain_spec.left
  exists ub
  intro x hx
  apply spec
  suffices Set.maxChain r = insert x (Set.maxChain r) by rw [this]; simp
  apply Set.maxChain_spec.right
  apply Set.IsChain.insert
  apply Set.maxChain_spec.left
  intro y mem; right; right
  apply htrans _ hx
  apply spec
  assumption
  intro; apply Or.inr

namespace Zorn

variable [LE α] [LT α]

public theorem preorder
  [IsPreorder α] (h: ∀c: Set α, Set.IsChain (· ≤ ·) c -> c.boundedAbove) :
  ∃m: α, ∀a, m ≤ a -> a ≤ m :=
  exists_maximal_of_bounded_chains <| by
  intro c hc; obtain ⟨ub, hub⟩ := h c hc
  exists ub

public theorem partialorder
  [IsPartialOrder α] (h: ∀c: Set α, Set.IsChain (· ≤ ·) c -> c.boundedAbove) :
  ∃m: α, ∀a, m ≤ a -> a = m := by
    obtain ⟨m, hm⟩ := preorder h
    exists m; intro a ha
    apply le_antisymm
    apply hm; all_goals assumption

public theorem preorder_in
  [IsPreorder α] (U: Set α) (h: ∀c ⊆ U, Set.IsChain (· ≤ ·) c -> (U ∩ c.upperBounds).Nonempty) :
  ∃m ∈ U, ∀a ∈ U, m ≤ a -> a ≤ m := by
  have := lift_trans (Set.inducedEmb (· ≤ ·: α -> α -> Prop) U)
  obtain ⟨ub, hub⟩ := exists_maximal_of_bounded_chains (α := U) (r := Set.Induced (· ≤ ·: α -> α -> Prop) U) <| by
    intro c hc
    have ⟨ub, ub_in_u, h⟩ := h (c.image Subtype.val) ?_ ?_
    dsimp at h; exists ⟨ub, ub_in_u⟩
    intro x hx
    exact h x.val (Set.mem_image' hx)
    intro x hx; simp at hx
    obtain ⟨_, _⟩ := hx; assumption
    refine ⟨?_⟩
    intro ⟨a, ha⟩ ⟨b, hb⟩
    show a ≤ b ∨ _ ∨ b ≤ a
    simp at ha hb
    obtain ⟨a_in_u, a_in_c⟩ := ha
    obtain ⟨b_in_u, b_in_c⟩ := hb
    rcases hc.connected ⟨⟨a, a_in_u⟩, a_in_c⟩ ⟨⟨b, b_in_u⟩, b_in_c⟩ with h | h | h
    left; assumption
    right; left; cases h; rfl
    right; right; assumption
  exists ub; apply And.intro ub.property; intro a a_in_u ub_le_a
  exact hub ⟨a, a_in_u⟩ ub_le_a

public theorem partialorder_in
  [IsPartialOrder α] (U: Set α) (h: ∀c ⊆ U, Set.IsChain (· ≤ ·) c -> (U ∩ c.upperBounds).Nonempty) :
  ∃m ∈ U, ∀a ∈ U, m ≤ a -> a = m := by
  have ⟨m, m_in_U, h⟩ := preorder_in U h; exists m
  apply And.intro m_in_U
  intro a a_in_U ha
  apply le_antisymm _ ha
  exact  h _ a_in_U ha
