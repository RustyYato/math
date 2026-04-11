import LeanMath.Topology.Limit.Defs
import LeanMath.Topology.Defs

open Order.Filter
open TopologicalSpace

namespace Limit

variable [TopologicalSpace α]

private def nhds' (a: α) : Order.Filter (Set α) :=
  -- the smallest filter of open sets which which contains `a`
  ⨅x: (OpenSets α).sep (a ∈ ·), 𝓟 x.val

private def mem_nhds' {a: α} : ∀{s}, s ∈ nhds' a ↔ ∃ t ⊆ s, t ∈ OpenSets α ∧ a ∈ t := by
  intro s; apply Iff.intro
  · intro h
    induction h with
    | @min X Y hx hy ihx ihy =>
      obtain ⟨t, ht, t_open, a_mem_t⟩ := ihx
      obtain ⟨u, hu, u_open, a_mem_u⟩ := ihy
      refine ⟨t ∩ u, ?_, ?_, ?_⟩
      intro x ⟨x_in_t, x_in_y⟩
      apply And.intro
      apply ht; assumption
      apply hu; assumption
      apply OpenSets.inter
      assumption
      assumption
      apply And.intro
      assumption
      assumption
    | @ge X hx Y hY ih =>
      obtain ⟨t, ht, t_open, a_mem_t⟩ := ih
      exact ⟨t, Set.sub_trans ht hY, t_open, a_mem_t⟩
    | of X hX =>
      simp at hX
      rcases hX with rfl | hX
      exact ⟨⊤, Set.sub_refl _, OpenSets.univ, True.intro⟩
      obtain ⟨_, ⟨_, ⟨x, ⟨x_open, a_in_x⟩, rfl⟩, rfl⟩, x_le_X⟩ := hX
      exact ⟨x, x_le_X, x_open, a_in_x⟩
  · intro ⟨x, x_sub_s, x_open, a_in_x⟩
    apply generate_of
    simp; refine ⟨_, ⟨_, ⟨x, ⟨x_open, a_in_x⟩, rfl⟩, rfl⟩, ?_⟩
    assumption

def nhds (a: α) : Limit α where
  toFilter := nhds' a
  ne_bot := by
    intro h
    rw [Order.Filter.eq_bot_iff_mem_bot, mem_nhds'] at h
    obtain ⟨t, ht, t_open, a_in_t⟩ := h
    have := ht a a_in_t
    contradiction

-- @[inherit_doc]
scoped notation "𝓝" => nhds

private def mem_nhds {a: α} : ∀{s}, s ∈ 𝓝 a ↔ ∃ t ⊆ s, t ∈ OpenSets α ∧ a ∈ t := mem_nhds'

def IsLimit (f: Order.Filter (Set α))  (x: α) : Prop := f ≤ 𝓝 x

noncomputable def limit [Nonempty α] (f: Order.Filter (Set α)) : α :=
  Classical.epsilon (IsLimit f)

end Limit
