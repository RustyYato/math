module

import Math.Tactic.Basic

namespace List

public theorem nodup_eraseDups [BEq α] [LawfulBEq α] (as: List α) : as.eraseDups.Nodup := by
  induction len_eq:as.length using Nat.strongRecOn generalizing as with
  | _ len ih =>
  cases as with
  | nil => rw [List.eraseDups_nil]; apply List.nodup_nil
  | cons a as =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    apply And.intro
    · intro h; simp at h
    · subst len
      replace ih (bs: List α) (h) := ih bs.length h bs rfl
      apply ih
      apply flip Nat.lt_of_le_of_lt
      apply Nat.lt_succ_self
      apply List.length_filter_le

public theorem perm_map (f: α -> β) {as bs: List α} (h: as ≈ bs) : as.map f ≈ bs.map f := by
  induction h with
  | nil => apply List.Perm.nil
  | swap => apply List.Perm.swap
  | cons => apply List.Perm.cons; assumption
  | trans => apply List.Perm.trans <;> assumption

public theorem perm_filter (f: α -> Bool) {as bs: List α} (h: as ≈ bs) : as.filter f ≈ bs.filter f := by
  induction h with
  | nil => apply List.Perm.nil
  | swap =>
    iterate 4 rw [List.filter_cons]
    split  <;> split
    apply List.Perm.swap
    apply List.Perm.cons
    apply List.Perm.refl
    apply List.Perm.cons
    apply List.Perm.refl
    apply List.Perm.refl
  | cons =>
    rw [List.filter_cons, List.filter_cons]; split
    apply List.Perm.cons
    assumption
    assumption
  | trans => apply List.Perm.trans <;> assumption

public theorem nodup_filter (f: α -> Bool) (as: List α) : as.Nodup -> (as.filter f).Nodup := by
  intro h; induction as with
  | nil => apply List.Pairwise.nil
  | cons a as ih =>
    rw [List.filter_cons]
    have ⟨not_mem, h⟩ := List.nodup_cons.mp h
    split
    apply List.nodup_cons.mpr
    apply And.intro _ (ih h)
    intro g; apply not_mem
    simp at g; exact g.left
    apply ih; assumption

public inductive MinCount (a: α) : List α -> ℕ -> Prop where
| nil : MinCount a [] 0
| cons : MinCount a xs n -> MinCount a (x::xs) n
| head : MinCount a as n -> MinCount a (a::as) (n + 1)

public theorem perm_ext_iff_of_nodup' {as bs : List α} (ha : as.Nodup) (hb : bs.Nodup) :
  as ~ bs ↔ ∀ (a : α), a ∈ as ↔ a ∈ bs := by
  apply Iff.intro
  · intro h x
    apply h.mem_iff
  intro h
  induction ha generalizing bs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons b bs => nomatch (h b).mpr (.head _)
  | @cons a as head ha ih =>
    obtain ⟨bs₀, bs₁, rfl⟩ := List.mem_iff_append.mp ((h a).mp (.head _))
    apply flip List.Perm.trans
    apply List.perm_cons_append_cons; rfl
    apply List.Perm.cons
    have perm := List.perm_cons_append_cons a (List.Perm.refl (bs₀ ++ bs₁))
    replace hb := perm.nodup_iff.mpr hb
    apply ih
    · exact (List.nodup_cons.mp hb).right
    · intro x
      apply Iff.intro
      intro hx
      cases perm.mem_iff.mpr <| (h x).mp (.tail _ hx)
      nomatch head _ hx rfl
      assumption
      intro hx
      rcases (h x).mpr (perm.mem_iff.mp (.tail _ hx)) with h | h
      have := (List.nodup_cons.mp hb).left; contradiction
      assumption

public theorem nodup_map (f: α -> β) (hf: Function.Injective f) (as: List α) (ha: as.Nodup) : (as.map f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj h
  rw [List.getElem_map, List.getElem_map] at h
  exact List.nodup_iff_eq_of_getElem_eq.mp ha _ _ _ _ (hf h)
