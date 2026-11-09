module

public import Math.Order.Set
import Math.Data.Set.Basic

namespace Math

namespace Set

variable {α: Type*}

@[expose] public def inducedEmb (r: α -> α -> Prop) (U: Set α) : Induced r U ↪r r where
  toFun := Subtype.val
  injective := by intro ⟨a, ha⟩ ⟨b, hb⟩ rfl; rfl
  map_rel_iff := Iff.rfl

@[expose] public def inducedEmbSub (r: α -> α -> Prop) (U V: Set α) (h: U ⊆ V) : Induced r U ↪r Induced r V where
  toFun x := {
      val := x.val
      property := h _ x.property
  }
  injective := by intro ⟨a, ha⟩ ⟨b, hb⟩ h; dsimp at h; cases h; rfl
  map_rel_iff := Iff.rfl

public abbrev IsChain (r: α -> α -> Prop) (U: Set α) := IsConnected (Induced r U) (· = ·)

@[expose] public def IsSuperChain (r: α -> α -> Prop) (a b: Set α) : Prop :=
  a ≤ b ∧ b.IsChain r
@[expose] public def IsStrictSuperChain (r: α -> α -> Prop) (a b: Set α) : Prop :=
  a < b ∧ b.IsChain r
@[expose] public def IsMaxChain (r: α -> α -> Prop) (U: Set α) : Prop :=
  U.IsChain r ∧ ∀s: Set α, s.IsChain r -> U ⊆ s -> U = s

variable {r: α -> α -> Prop}

public noncomputable def succChain (r: α -> α -> Prop) (U: Set α) : Set α :=
  open Classical in
  if h:∃s: Set α, IsStrictSuperChain r U s then
    Classical.choose h
  else
    U

public theorem sub_succChain (r: α -> α -> Prop) (U: Set α) : U ⊆ U.succChain r := by
  unfold succChain; split <;> rename_i h
  exact (Classical.choose_spec h).left.left
  rfl

inductive ChainClosure (r: α -> α -> Prop): Set α -> Prop where
| union : ∀ {s: Set (Set α)}, (∀ a ∈ s, ChainClosure r a) → ChainClosure r (⋃ s)
| succ : ∀ {s}, ChainClosure r s -> ChainClosure r (succChain r s)

public def maxChainSet (r: α -> α -> Prop) : Set (Set α) where
  Mem := ChainClosure r
public def maxChain (r: α -> α -> Prop) := ⋃ maxChainSet r

theorem succChain.toIsMaxChain {s: Set α} (hs: IsChain r s) (h: succChain r s = s) : IsMaxChain r s := by
  unfold succChain at h
  split at h; rename_i g
  have := Classical.choose_spec g
  rw [h] at this
  nomatch this.left.right (le_refl _)
  apply And.intro
  assumption
  intro U hU hs
  apply Set.sub_antisymm
  assumption
  rename_i h'
  simp at h'
  replace h' := h' U
  simp [IsStrictSuperChain] at h'
  replace h' := (h' ⟨hs, ·⟩ hU)
  simp at h'
  assumption

namespace IsChain

variable {s t: Set α}

public theorem empty : IsChain r ⊥ where
  connected := nofun
public theorem univ [IsConnected r (· = ·)] : IsChain r ⊤ :=
  lift_connected (inducedEmb r ⊤)
public theorem to_subset (h: s ⊆ t) (chain: IsChain r t) : IsChain r s :=
  lift_connected (inducedEmbSub r _ _ h)

public theorem insert (c: IsChain r s) (x: α) (h: ∀y ∈ s, r x y ∨ x = y ∨ r y x) : IsChain r (insert x s) where
  connected := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simp [Induced]
    simp at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    right; left; rfl
    apply h
    assumption
    rcases (h a ha) with g | g | g
    right; right; assumption
    right; left; symm; assumption
    left; assumption
    rcases connected (R := s.Induced r) ⟨_, ha⟩ ⟨_, hb⟩ with h | h | h
    left; assumption
    right; left; exact Subtype.mk.inj h
    right; right; assumption

public theorem sInter {t: Set (Set α)} (h: t.Nonempty) (c: ∀s ∈ t, IsChain r s) : IsChain r (⋂ t) :=
  have ⟨s, mem⟩ := h
  have := c s mem
  lift_connected <| inducedEmbSub r (⋂ t) s <| by
    intro x hx; apply hx; assumption

public theorem succ (U: Set α) (hu: U.IsChain r) : IsChain r (U.succChain r) := by
  unfold succChain
  split <;> rename_i h
  exact (Classical.choose_spec h).right
  assumption

end IsChain

namespace ChainClosure

theorem empty : ChainClosure r ⊥ := by
  rw [←Set.sUnion_empty]
  apply ChainClosure.union
  nofun

theorem maxChain : ChainClosure r (maxChain r) := by
  apply ChainClosure.union
  intro x hx
  assumption

theorem total_aux (cs: ChainClosure r s)
    (h : ∀ ⦃x⦄, ChainClosure r x → x ⊆ t → x = t ∨ succChain r x ⊆ t)
    : s ⊆ t ∨ succChain r t ⊆ s := by
  induction cs with
  | succ =>
    rename_i s cs ih
    rcases ih with ih | ih
    rcases h cs ih with eq | succ_le
    subst t
    right; rfl
    left; assumption
    right
    apply Set.sub_trans ih
    apply sub_succChain
  | union =>
    rename_i U cU ih
    apply Classical.or_iff_not_imp_right.mpr
    intro g
    intro x ⟨s, hs, hx⟩
    apply (ih s hs).resolve_right
    intro h
    apply g
    apply Set.sub_trans h
    intro y hy
    simp
    exists s
    assumption

theorem eq_or_succ_sub_of_sub
  (cs: ChainClosure r s) (ct: ChainClosure r t) (h: s ⊆ t): s = t ∨ succChain r s ⊆ t := by
  induction ct generalizing s with
  | succ =>
    rename_i t ct ih
    rcases (total_aux cs (fun _ => ih)) with s_sub_t | succ_t_sub_s
    right
    obtain rfl | succ_s_sub_t := ih cs s_sub_t
    rfl
    apply Set.sub_trans succ_s_sub_t
    apply sub_succChain
    left
    apply Set.sub_antisymm <;> assumption
  | union =>
    rename_i t ct ih
    apply Or.imp_left (Set.sub_antisymm h)
    apply Classical.byContradiction
    have : ⋃t ⊆ s ↔ ∀x ∈ t, x ⊆ s := by
      apply Iff.intro; intro g
      intro x hx y hy
      apply g
      simp
      exists x
      intro h x ⟨y, hy, hx⟩
      apply h <;> assumption
    rw [this, not_or, Classical.not_forall]
    intro ⟨⟨x, h₀⟩, h₁⟩
    rw [not_imp] at h₀
    obtain ⟨x_in_t, not_x_sub_s⟩ := h₀
    have cx := ct x x_in_t
    rcases total_aux cs (fun _ => ih x x_in_t) with s_sub_x | succ_x_sub_s
    · obtain rfl | s := ih x x_in_t cs s_sub_x
      contradiction
      rename_i s'
      apply h₁
      apply Set.sub_trans s
      intro y hy; simp
      exists x
    apply not_x_sub_s
    apply Set.sub_trans _ succ_x_sub_s
    apply sub_succChain

theorem total (cs: ChainClosure r s) (ct: ChainClosure r t) : s ⊆ t ∨ t ⊆ s := by
  cases total_aux cs (fun _ h => eq_or_succ_sub_of_sub h ct)
  left; assumption
  right
  rename_i h
  apply Set.sub_trans _ h
  apply sub_succChain

theorem IsChain (c: ChainClosure r s) : IsChain r s := by
  induction c with
  | succ => apply IsChain.succ; assumption
  | @union U hU ih =>
    refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
    rename_i x y ; clear x y
    show r a b ∨ _ ∨ r b a
    obtain ⟨A, A_in_U, ha⟩ := ha
    obtain ⟨B, B_in_U, hb⟩ := hb
    rcases total (hU _ A_in_U) (hU _ B_in_U) with h | h
    · rcases (ih _ B_in_U).connected (R := Induced r B) ⟨a, h _ ha⟩ ⟨b, hb⟩ with h | h | h
      left; assumption
      right; left; cases h; rfl
      right; right; assumption
    · rcases (ih _ A_in_U).connected (R := Induced r A) ⟨a, ha⟩ ⟨b, h _ hb⟩ with h | h | h
      left; assumption
      right; left; cases h; rfl
      right; right; assumption

end ChainClosure

theorem maxChain_succ (r: α -> α -> Prop) : (maxChain r).succChain r = maxChain r := by
  have := ChainClosure.union (s := {(maxChain r).succChain r}) (r := r) (by
      intro x hx; cases hx
      apply ChainClosure.succ
      apply ChainClosure.maxChain)
  rw [sUnion_singleton] at this
  symm; ext x; apply Iff.intro
  apply Set.sub_succChain
  intro hx
  unfold maxChain
  apply Set.mem_sUnion.mpr
  refine ⟨_, ?_, hx⟩
  assumption

public theorem maxChain_spec : IsMaxChain r (maxChain r) := by
  apply succChain.toIsMaxChain
  apply ChainClosure.IsChain
  apply ChainClosure.maxChain
  rw [maxChain_succ]
