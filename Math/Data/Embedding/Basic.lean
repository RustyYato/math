module

public import Math.Data.Embedding.Defs
import Math.Data.Equiv.Basic

namespace Math.Embedding

public def erase_none (f: Option α ↪ Option β) : α ↪ β where
  toFun a :=
    if ha:f a = .none then
      (f .none).get <| by
        rw [Option.isSome_iff_ne_none]
        intro g; rw [←g] at ha
        nomatch f.inj ha
    else
      (f a).get <| by
        rwa [Option.isSome_iff_ne_none]
  injective := by
    intro a b h; dsimp at h
    split at h <;> split at h <;> rename_i h₀ h₁
    all_goals replace h := Option.get_inj.mp h
    · rw [←h₁] at h₀
      cases f.inj h₀; rfl
    · nomatch f.inj h
    · nomatch f.inj h
    · exact Option.some.inj (f.inj h)

@[expose] public def fin (h: n ≤ m) : Fin n ↪ Fin m where
  toFun x := {
    val := x.val
    isLt := Nat.lt_of_lt_of_le x.isLt h
  }
  injective := by intro ⟨a, _⟩ ⟨b, _⟩ h; cases h; rfl

public theorem of_fin (f: Fin n ↪ Fin m) : n ≤ m := by
  induction n generalizing m with
  | zero => apply Nat.zero_le
  | succ n ih =>
    cases m with
    | zero => exact (f 0).elim0
    | succ m =>
      apply Nat.succ_le_succ
      apply ih
      replace f := Equiv.congr_embedding Equiv.fin_succ Equiv.fin_succ f
      exact erase_none f
