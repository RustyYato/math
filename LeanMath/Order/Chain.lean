import LeanMath.Data.Set.Defs
import LeanMath.Order.Defs

namespace Set

section

variable (r: α -> α -> Prop)

def Induced(U: Set α) : U -> U -> Prop := fun x y => r x y

def Induced.embed (s: Set α) : s.Induced r ↪r r where
  toFun x := x.val
  inj := Subtype.val_inj
  map_rel := Iff.rfl

def Induced.embedSub {s t: Set α} (h: s ⊆ t) : s.Induced r ↪r t.Induced r where
  toFun x := ⟨x.val, h _ x.property⟩
  inj := by
    intro ⟨x, _⟩ ⟨y, _⟩ eq
    dsimp at eq
    cases eq
    rfl
  map_rel := Iff.rfl

def Induced.embedSInter {s: Set α} {t: Set (Set α)} (h: s ∈ t) : (⋂t).Induced r ↪r s.Induced r :=
  Induced.embedSub r <| by
    intro x h
    apply h
    assumption

abbrev IsChain (U: Set α) := Relation.IsTrichotomous (U.Induced r) (· = ·)

instance {U: Set α} [Relation.IsRefl r] : Relation.IsRefl (U.Induced r) where
  refl _ := Relation.refl (R := r) _

instance {U: Set α} [IsChain r U] [Relation.IsRefl r] : Relation.IsTotal (U.Induced r) := inferInstance

def IsSuperChain (s u: Set α) :=
  s ⊆ u ∧ u.IsChain r
def IsStrictSuperChain (s u: Set α) :=
  s ⊂ u ∧ u.IsChain r
def IsMaxChain (s: Set α) :=
  s.IsChain r ∧ ∀x, x.IsChain r -> s ⊆ x -> s = x

end

variable {r: α -> α -> Prop}

namespace IsChain

def empty : IsChain R ∅ where
  trichotomous := nofun

def univ [Relation.IsTrichotomous R (· = ·)] : IsChain R ⊤ where
  trichotomous x y := by
    rcases Relation.trichotomous R x.val y.val with h | h | h
    left; assumption
    right; left; apply Subtype.val_inj; assumption
    right; right; assumption

def ofSubset (h: s ⊆ t) (c: IsChain r t) : IsChain r s :=
  (Induced.embedSub r h).liftTrichotomous

def insert (c: IsChain r s) (x: α) (h: ∀y ∈ s, r x y ∨ x = y ∨ r y x) : IsChain r (insert x s) where
  trichotomous := by
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
    rcases Relation.trichotomous (s.Induced r) ⟨_, ha⟩ ⟨_, hb⟩ with h | h | h
    left; assumption
    right; left; exact Subtype.mk.inj h
    right; right; assumption

def sInter {t: Set (Set α)} (h: t.Nonempty) (c: ∀s ∈ t, IsChain r s) : IsChain r (⋂ t) :=
  have ⟨s, mem⟩ := h
  have := c s mem
  (Induced.embedSInter r mem).liftTrichotomous

def inter (cs: IsChain r s) (ct: IsChain r t) : IsChain r (s ∩ t) := by
  rw [←Set.sInter_pair_eq_inter]
  apply sInter
  infer_instance
  intro x mem
  simp at mem; rcases mem with rfl | rfl <;> assumption

noncomputable def succChain (r: α -> α -> Prop) (s: Set α) :=
  open scoped Classical in
  if h:∃t, IsStrictSuperChain r s t then
    Classical.choose h
  else
    s

def succChain.isStrictSuperChain {s: Set α} (h: ∃t, IsStrictSuperChain r s t) :
  IsStrictSuperChain r s (succChain r s) := by
  unfold succChain
  rw [dif_pos h]
  exact Classical.choose_spec h
def succChain.sub (s: Set α) :
  s ⊆ succChain r s := by
  unfold succChain
  split
  rename_i h
  have := Classical.choose_spec h
  exact this.left.left
  rfl
def succChain.isChain' {s: Set α} (h: ∃t, IsStrictSuperChain r s t) :
  IsChain r s := (isStrictSuperChain h).right.ofSubset (sub _)
def succChain.isChain {s: Set α} (h: ∃t, IsStrictSuperChain r s t) :
  IsChain r (succChain r s) := (isStrictSuperChain h).right

def succChain.ofIsMaxChain {s: Set α} (h: IsMaxChain r s) : succChain r s = s := by
  unfold succChain
  rw [dif_neg]
  intro ⟨t, ssup⟩
  have := h.right t ssup.right ssup.left.left
  have ⟨x, hx, hy⟩ := ssup.left.right
  rw [this] at hy
  contradiction

def succChain.toIsMaxChain {s: Set α} (hs: IsChain r s) (h: succChain r s = s) : IsMaxChain r s := by
  unfold succChain at h
  split at h; rename_i g
  have := Classical.choose_spec g
  rw [h] at this
  nomatch this.left.right
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

def exists_succChain_of_not_max_chain (c: IsChain r s) (h: ¬IsMaxChain r s) : ∃t, IsStrictSuperChain r s t := by
  replace ⟨t, h⟩ := Classical.not_forall.mp (not_and.mp h c)
  replace ⟨ct, h⟩ := not_imp.mp h
  replace ⟨s_sub_t, h⟩ := not_imp.mp h
  exists t
  refine ⟨⟨s_sub_t, ?_⟩, ct⟩
  apply Classical.byContradiction
  intro g; simp at g
  apply h
  apply Set.sub_antisymm <;> assumption

def succ (c: IsChain r s) : IsChain r (succChain r s) := by
  by_cases h:IsMaxChain r s
  rw [succChain.ofIsMaxChain h]
  assumption
  apply succChain.isChain
  exact exists_succChain_of_not_max_chain c h

inductive ChainClosure (r: α -> α -> Prop): Set α -> Prop where
| union : ∀ {s: Set (Set α)}, (∀ a ∈ s, ChainClosure r a) → ChainClosure r (⋃ s)
| succ : ∀ {s}, ChainClosure r s -> ChainClosure r (succChain r s)

def _root_.Set.maxChain (r: α -> α -> Prop) := ⋃ Set.ofMem (ChainClosure r)

namespace ChainClosure

def empty : ChainClosure r ⊥ := by
  rw [←Set.sUnion_empty]
  apply ChainClosure.union
  intros
  contradiction

def maxChain : ChainClosure r (maxChain r) := by
  apply ChainClosure.union
  intros; assumption

def total_aux (cs: ChainClosure r s)
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
    apply succChain.sub
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

def eq_or_succ_sub_of_sub
  (cs: ChainClosure r s) (ct: ChainClosure r t) (h: s ⊆ t): s = t ∨ succChain r s ⊆ t := by
  induction ct generalizing s with
  | succ =>
    rename_i t ct ih
    rcases (total_aux cs (fun _ => ih)) with s_sub_t | succ_t_sub_s
    right
    obtain rfl | succ_s_sub_t := ih cs s_sub_t
    rfl
    apply Set.sub_trans succ_s_sub_t
    apply succChain.sub
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
    apply succChain.sub

def total (cs: ChainClosure r s) (ct: ChainClosure r t) : s ⊆ t ∨ t ⊆ s := by
  cases total_aux cs (fun _ h => eq_or_succ_sub_of_sub h ct)
  left; assumption
  right
  rename_i h
  apply Set.sub_trans _ h
  apply succChain.sub

def IsChain (c: ChainClosure r s) : IsChain r s := by
  induction c with
  | succ c ih => exact ih.succ
  | union c ih =>
    apply Relation.IsTrichotomous.mk
    intro ⟨a, amem⟩ ⟨b, bmem⟩
    unfold Induced; dsimp
    rw [Set.mem_sUnion] at amem bmem
    obtain ⟨sa, sa_in_s, a_in_sa⟩ := amem
    obtain ⟨sb, sb_in_s, b_in_sb⟩ := bmem
    have sa_chain := ih sa sa_in_s
    have sb_chain := ih sb sb_in_s
    rcases total (c _ sa_in_s) (c _ sb_in_s) with sa_sub_sb | sb_sub_sa
    rcases sb_chain.trichotomous ⟨_, sa_sub_sb _ a_in_sa⟩ ⟨_, b_in_sb⟩ with h | h | h
    left; assumption
    right; left; cases h; congr
    right; right; assumption
    rcases sa_chain.trichotomous ⟨_, a_in_sa⟩ ⟨_, sb_sub_sa _ b_in_sb⟩ with h | h | h
    left; assumption
    right; left; cases h; congr
    right; right; assumption

end ChainClosure

end IsChain

open IsChain in
def maxChain_spec : IsMaxChain r (maxChain r) := by
  apply succChain.toIsMaxChain
  apply ChainClosure.IsChain
  apply ChainClosure.maxChain
  apply flip Set.sub_antisymm
  apply succChain.sub
  apply Set.sub_sUnion
  apply ChainClosure.succ
  apply ChainClosure.maxChain

end Set
