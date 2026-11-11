module

public import Math.Data.Multiset.Defs
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

@[ext] public theorem ext (a b: Finset α) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  congr; replace h : ∀x, x ∈ a ↔ x ∈ b := h
  induction a using Multiset.ind with | _ a =>
  induction b using Multiset.ind with | _ b =>
  apply Multiset.sound
  apply (List.perm_ext_iff_of_nodup ha hb).mpr
  apply h

public theorem mem_ofMultiset [DecidableEq α] (ms: Multiset α) : ∀x, x ∈ ofMultiset ms ↔ x ∈ ms := by
  intro x ; show x ∈ ms.eraseDups ↔ x ∈ ms
  rw [Multiset.mem_eraseDups]

public theorem mem_ofList [DecidableEq α] (as: List α) : ∀x, x ∈ ofList as ↔ x ∈ as := by
  apply mem_ofMultiset

end Finset
