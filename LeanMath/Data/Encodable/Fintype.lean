import LeanMath.Data.Encodable.Defs
import LeanMath.Data.Fintype.Defs

namespace Encodable.ofFintype

variable [Encodable α] [Fintype α]

local instance : DecidableEq α :=
  fun a b => decidable_of_iff (Equiv.encoding α a = Equiv.encoding α b) (by
    apply Function.Injective.eq_iff
    apply inj (Equiv.encoding _))

-- private def list_dedup : List α -> List α :=
--   List.foldr (fun x acc => if x ∈ acc then acc else x::acc) []

private def list_length_le (a b: List α) (ha: a.Sublist b) : a.length ≤ b.length := by
  induction ha with
  | slnil => apply Nat.le_refl
  | cons =>
    apply Nat.le_trans
    assumption
    apply Nat.le_succ
  | cons₂ =>
    apply Nat.succ_le_succ
    assumption

private def list_count_eq_one (x: α) (a: List α) (hx: x ∈ a) (ha: a.Nodup) : a.count x = 1 := by
  induction hx with
  | head =>
    rw [List.count_cons_self, List.count_eq_zero_of_not_mem]
    intro h; apply (List.nodup_cons.mp ha).left
    assumption
  | tail _ _ ih =>
    rw [List.count_cons_of_ne]
    apply ih
    apply ha.tail
    intro rfl
    apply (List.nodup_cons.mp ha).left
    assumption

private def list_ofFn_nodup (f: Fin n -> α) (hf: Function.Injective f) : (List.ofFn f).Nodup := by
  induction n with
  | zero => apply List.Pairwise.nil
  | succ n ih =>
    rw [List.ofFn_succ]
    apply List.nodup_cons.mpr; apply And.intro
    · simp; intro x h
      exact Fin.succ_ne_zero _ (hf h)
    · apply ih
      apply Function.Injective.comp
      assumption
      intro _ _
      apply Fin.succ_inj.mp

private def list_pmap_nodup {P: α -> Prop} (xs: List α) (f: ∀x, P x -> β) (hx: ∀x ∈ xs, P x) (h: xs.Nodup) (hf: ∀x y (hx: P x) (hy: P y), f x hx = f y hy -> x = y) : (xs.pmap f hx).Nodup := by
  induction h with
  | nil => apply List.Pairwise.nil
  | @cons a as ha has ih =>
    apply List.nodup_cons.mpr; apply And.intro
    · simp; intro h
      intro x hx
      cases hf _ _ _ _ hx
      exact ha _ x rfl
    · apply ih

private def list_attach_nodup (xs: List α) (h: xs.Nodup) : xs.attach.Nodup := by
  apply list_pmap_nodup
  assumption
  intro x y hx hy h
  exact Subtype.mk.inj h

private def toList (acc: List α) (hacc: acc.Nodup) : List α :=
  if h:Fintype.card α = acc.length then
    acc
  else
    have : ∃x, x ∉ acc := by
      apply Decidable.byContradiction
      intro g
      rw [Decidable.not_exists_not] at g
      apply h; clear h
      rename_i ft; induction ft with | _ card ra =>
      obtain ⟨ra, h⟩ := ra; dsimp; clear h
      let := List.ofFn ra
      rw [←List.length_ofFn (f := ra)]
      apply List.Perm.length_eq
      apply List.perm_iff_count.mpr
      intro a
      iterate 2 rw [list_count_eq_one]
      apply g; assumption
      simp; apply ra.surj
      apply list_ofFn_nodup
      exact inj ra
    toList (Encodable.choice this::acc) <| by
      apply List.Pairwise.cons _ hacc
      intro x hx rfl
      exact Encodable.choice_spec this hx
termination_by Fintype.card α - acc.length
decreasing_by
  have : acc.length < Fintype.card α := ?_
  simp; omega
  apply Nat.lt_of_le_of_ne _ (Ne.symm h)
  rw [←List.length_attach]
  let ft := Fintype.ofList acc.attach ?_ ?_
  show ft.card ≤ _
  rename_i ft'
  · induction Fintype.truncFinEncodable ft with | _ et =>
    induction Fintype.truncFinEncodable ft' with | _ et' =>
    rw [Fintype.card_eq_finencodable, Fintype.card_eq_finencodable]
    apply FinEncodable.card_le
    apply Embedding.subtype_val
  · apply list_attach_nodup
    assumption
  · intro x; apply List.mem_attach

scoped instance : FinEncodable α where
  card := Fintype.card α
  bij := sorry
  try_decode := sorry

end Encodable.ofFintype
