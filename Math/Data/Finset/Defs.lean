module

public import Math.Data.Multiset.Defs
import Math.Data.List.Defs
import Math.Tactic.Basic

namespace Math

@[expose] section

public structure Finset (α: Type*) where
  toMultiset : Multiset α
  nodup: toMultiset.Nodup

namespace Finset

public def ofMultiset [DecidableEq α] (ms: Multiset α) : Finset α where
  toMultiset := ms.eraseDups
  nodup := ms.nodup_eraseDups
public def ofList [DecidableEq α] : List α -> Finset α := ofMultiset ∘ Multiset.mk

public instance : Membership α (Finset α) where
  mem s a := a ∈ s.toMultiset

public instance : HasSubset (Finset α) where
  Subset a b := ∀x ∈ a, x ∈ b

public instance [DecidableEq α] (a: α) (s: Finset α) : Decidable (a ∈ s) :=
  inferInstanceAs (Decidable (a ∈ s.toMultiset))

@[ext] public theorem ext (a b: Finset α) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  congr; replace h : ∀x, x ∈ a ↔ x ∈ b := h
  induction a using Multiset.ind with | _ a =>
  induction b using Multiset.ind with | _ b =>
  apply Multiset.sound
  apply (List.perm_ext_iff_of_nodup' ha hb).mpr
  apply h

public def card (s: Finset α) : ℕ := s.toMultiset.length

public theorem mem_ofMultiset [DecidableEq α] (ms: Multiset α) : ∀x, x ∈ ofMultiset ms ↔ x ∈ ms := by
  intro x ; show x ∈ ms.eraseDups ↔ x ∈ ms
  rw [Multiset.mem_eraseDups]

public theorem mem_ofList [DecidableEq α] (as: List α) : ∀x, x ∈ ofList as ↔ x ∈ as := by
  apply mem_ofMultiset

@[no_expose]
public def union [DecidableEq α] (a b: Finset α) : Finset α where
  toMultiset := a.toMultiset ++ b.toMultiset.filter (· ∉ a)
  nodup := by
    apply Multiset.nodup_append.mpr
    apply And.intro a.nodup
    apply And.intro
    · apply Multiset.nodup_filter
      exact b.nodup
    · intro x hx hf
      simp at hf
      exact hf.right hx

@[no_expose]
public def inter [DecidableEq α] (a b: Finset α) : Finset α where
  toMultiset := a.toMultiset.filter (· ∈ b)
  nodup := by
    apply Multiset.nodup_filter
    exact a.nodup

@[no_expose]
public def sdiff [DecidableEq α] (a b: Finset α) : Finset α where
  toMultiset := a.toMultiset.filter (· ∉ b)
  nodup := by
    apply Multiset.nodup_filter
    exact a.nodup

public instance [DecidableEq α] : Union (Finset α) where
  union := union

public instance [DecidableEq α] : Inter (Finset α) where
  inter := inter

public instance [DecidableEq α] : SDiff (Finset α) where
  sdiff := sdiff

@[simp] public theorem mem_union [DecidableEq α] {a b: Finset α} : ∀{x}, x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  intro x; change x ∈ a.toMultiset ++ b.toMultiset.filter _ ↔ x ∈ a.toMultiset ∨ x ∈ b.toMultiset
  simp
  apply Iff.intro
  intro h; rcases h with h | ⟨h, _⟩
  left; assumption
  right; assumption
  intro h
  by_cases g:x ∈ a
  left; assumption
  right; cases h; contradiction
  apply And.intro <;> assumption

@[simp] public theorem mem_inter [DecidableEq α] {a b: Finset α} : ∀{x}, x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  intro x; change x ∈ a.toMultiset.filter _ ↔ _
  simp; intro; rfl

@[simp] public theorem mem_sdiff [DecidableEq α] {a b: Finset α} : ∀{x}, x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by
  intro x; change x ∈ a.toMultiset.filter _ ↔ _
  simp; intro; rfl

public instance : EmptyCollection (Finset α) where
  emptyCollection := {
    toMultiset := .nil
    nodup := List.nodup_nil
  }

@[simp] public theorem not_mem_empty (a: α) : a ∉ (∅: Finset α) := nofun

public theorem eq_union_of_superset [DecidableEq α] {a b: Finset α} (h: a ⊆ b) : ∃k: Finset α, b = a ∪ k ∧ ∀x, x ∉ a ∩ k := by
  exists b \ a
  apply And.intro
  · ext x; simp
    apply Iff.intro
    intro h
    by_cases hx:x ∈ a; left; assumption
    right; apply And.intro <;> assumption
    intro h; rcases h with _ | ⟨_, _⟩
    apply h; assumption
    assumption
  · simp; intros; assumption

public instance : Singleton α (Finset α) where
  singleton a := {
    toMultiset := a::ₘ.nil
    nodup := by
      apply List.nodup_cons.mpr
      apply And.intro nofun
      apply List.nodup_nil
  }

public instance [DecidableEq α] : Insert α (Finset α) where
  insert a s := {a} ∪ s

@[simp] public theorem mem_singleton {a: α} : ∀{x}, x ∈ ({a}: Finset α) ↔ x = a := by
  intro x; change x ∈ [a] ↔ _
  simp

@[simp] public theorem mem_insert [DecidableEq α] {a: α} {s: Finset α} : ∀{x}, x ∈ insert a s ↔ x = a ∨ x ∈ s := by
  intro x; change x ∈ ({a}: Finset α) ∪ s ↔ _
  simp

public def insert_unique (s: Finset α) (a: α) (ha: a ∉ s) : Finset α where
  toMultiset := a::ₘs.toMultiset
  nodup := by
    apply (Multiset.nodup_cons _ _).mpr
    exact And.intro ha s.nodup

@[simp] public theorem mem_insert_unique [DecidableEq α] {a: α} {s: Finset α} {ha: a ∉ s} : ∀{x}, x ∈ s.insert_unique a ha ↔ x = a ∨ x ∈ s := by
  intro x; change x ∈ Multiset.cons _ _ ↔ _
  simp; rfl

public theorem insert_unique_eq_insert [DecidableEq α] (s: Finset α) (a: α) (ha: a ∉ s) : s.insert_unique a ha = insert a s := by
  ext; simp

@[induction_eliminator]
public theorem induction
  {motive: Finset α -> Prop}
  (nil: motive ∅)
  (cons: ∀a (s: Finset α) (ha: a ∉ s), motive s -> motive (s.insert_unique a ha))
  (s: Finset α) : motive s := by
  obtain ⟨s, hs⟩ := s
  induction s with
  | nil => apply nil
  | cons a as ih =>
    simp [Multiset.nodup_cons] at hs
    obtain ⟨not_mem, hs⟩ := hs
    apply cons a ⟨as, hs⟩
    assumption
    apply ih

section

variable [DecidableEq α]

@[simp] public theorem empty_union (s: Finset α) : ∅ ∪ s = s := by ext; simp
@[simp] public theorem union_empty (s: Finset α) : s ∪ ∅ = s := by ext; simp
@[simp] public theorem empty_inter (s: Finset α) : ∅ ∩ s = ∅ := by ext; simp
@[simp] public theorem inter_empty (s: Finset α) : s ∩ ∅ = ∅ := by ext; simp

@[simp] public theorem insert_union (a: α) (s t: Finset α) : insert a s ∪ t = insert a (s ∪ t) := by ext; simp [or_assoc]
@[simp] public theorem union_insert (s: Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
  ext; simp
  rw [←or_assoc, ←or_assoc]; apply or_congr _ Iff.rfl
  apply or_comm

public theorem insert_unique_union (a: α) (s t: Finset α) (hs: a ∉ s) (ht: a ∉ t) : s.insert_unique a hs ∪ t = (s ∪ t).insert_unique a (by simp; trivial) := by ext; simp [or_assoc]
-- public theorem union_insert_unique (s: Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
--   ext; simp
--   rw [←or_assoc, ←or_assoc]; apply or_congr _ Iff.rfl
--   apply or_comm

end

end Finset
