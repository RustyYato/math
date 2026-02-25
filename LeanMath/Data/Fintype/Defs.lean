import LeanMath.Data.Bijection.Defs
import LeanMath.Data.Trunc.Defs
import LeanMath.Tactic.AxiomBlame

inductive POption (α: Sort u) where
| some (a: α)
| none

class Fintype.Repr (α: Sort u) (n: Nat) where
  bij: Fin n ↭ α
  try_decode: POption ({ f: α -> Fin n // Function.LeftInverse f bij })

class Fintype (α: Sort u) : Sort (max u 1) where
  card: Nat
  repr: Trunc (Fintype.Repr α card)

namespace Fintype

def card_eq (fa fb: Fintype α) : fa.card = fb.card := by
  obtain ⟨ca, fa⟩ := fa
  obtain ⟨cb, fb⟩ := fb
  induction fa with | mk fa =>
  induction fb with | mk fb =>
  show ca = cb
  obtain ⟨⟨fa, fainj, fasurj⟩, ha⟩ := fa
  obtain ⟨⟨fb, fbinj, fbsurj⟩, hb⟩ := fb
  clear ha hb
  have eqv : ∀a: α, (∃i, fa i = a) ↔ (∃i, fb i = a) := by
    intro a
    apply Iff.intro <;> intro
    apply fbsurj
    apply fasurj
  clear fasurj fbsurj
  induction ca generalizing cb with
  | zero =>
    cases cb with
    | zero => rfl
    | succ cb =>
      have ⟨i, _⟩ := (eqv (fb ⟨0, Nat.zero_lt_succ _⟩)).mpr ⟨_, rfl⟩
      exact i.elim0
  | succ ca ih =>
    have ⟨i, hi⟩ := (eqv (fa ⟨0, Nat.zero_lt_succ _⟩)).mp ⟨_, rfl⟩
    replace hi := hi.symm
    cases cb with
    | zero => exact i.elim0
    | succ cb =>
      congr
      refine ih ?_ ?_ ?_ ?_ ?_ ?_
      · exact fa ∘ Fin.succ
      · apply Function.Injective.comp
        assumption
        intro _ _
        apply Fin.succ_inj.mp
      · refine fun x => fb <| if hx:x.val < i.val then ⟨x.val, ?_⟩ else ⟨x.val + 1, ?_⟩
        · apply Nat.lt_trans hx
          exact i.isLt
        · apply Nat.succ_lt_succ
          exact x.isLt
      · apply Function.Injective.comp
        assumption
        intro a b h
        dsimp at h
        split at h <;> split at h
        · exact Fin.val_inj.mp (Fin.mk.inj h)
        · rename_i ha hb
          replace hb := Nat.le_of_not_lt hb
          replace h := Fin.mk.inj h
          rw [h] at ha
          have := Nat.not_le_of_lt (Nat.lt_of_lt_of_le ha hb) (Nat.le_succ _)
          contradiction
        · rename_i ha hb
          replace ha := Nat.le_of_not_lt ha
          replace h := Fin.mk.inj h
          rw [←h] at hb
          have := Nat.not_le_of_lt (Nat.lt_of_lt_of_le hb ha) (Nat.le_succ _)
          contradiction
        · exact Fin.val_inj.mp (Nat.succ.inj (Fin.mk.inj h))
      · intro a
        apply Iff.intro
        · intro ⟨x, hx⟩
          have ⟨y, hy⟩ := (eqv a).mp ⟨_, hx⟩
          refine if g:y.val < i.val then ?_ else ?_
          · exists ⟨y.val, ?_⟩
            apply Nat.lt_of_lt_of_le
            assumption
            apply Nat.le_of_lt_succ
            exact i.isLt
            dsimp
            rwa [if_pos g]
          · have : i.val < y.val := by
              apply Nat.lt_of_le_of_ne
              · apply Nat.le_of_not_lt
                assumption
              · intro h
                cases Fin.val_inj.mp h
                rw [←hi] at hy
                rw [←hy] at hx
                nomatch (Fin.mk.inj (fainj hx))
            match y with
            | ⟨y + 1, ylt⟩ =>
            exists ⟨y, ?_⟩
            · show y < cb
              apply Nat.lt_of_succ_lt_succ
              assumption
            · dsimp
              rw [dif_neg]
              apply Eq.trans _ hy
              congr
              apply Nat.not_lt_of_le
              apply Nat.le_of_lt_succ
              assumption
        · intro ⟨x, hx⟩
          have ⟨y, hy⟩ := (eqv a).mpr ⟨_, hx⟩
          match y with
          | ⟨0, _⟩ =>
            replace hy := hi.symm.trans hy
            replace hx := fbinj (hx.trans hy.symm)
            exfalso
            split at hx
            rename_i h
            rw [←hx] at h
            exact Nat.lt_irrefl _ h
            rename_i h
            rw [←hx] at h
            exact h (Nat.lt_succ_self _)
          | ⟨y + 1, hy⟩ =>
            exists ⟨y, ?_⟩
            apply Nat.lt_of_succ_lt_succ
            assumption
            assumption

instance : Subsingleton (Fintype α) where
  allEq a b := by
    have card_eq := card_eq a b
    obtain ⟨ca, a⟩ := a
    obtain ⟨cb, b⟩ := b
    cases card_eq
    congr
    apply Subsingleton.allEq

instance : Fintype (Fin n) where
  card := n
  repr := Trunc.mk {
    bij := Bijection.id _
    try_decode := .some <| {
      val := id
      property _ := rfl
    }
  }

instance : Fintype Bool where
  card := 2
  repr := Trunc.mk {
    bij := {
      toFun
      | ⟨0, _⟩ => false
      | ⟨1, _⟩ => true
      | ⟨n + 2, h⟩ => by
        replace h := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)
        contradiction
      inj' := by
        intro a b h
        refine match a with
        | ⟨0, _⟩ => ?_
        | ⟨1, _⟩ => ?_
        | ⟨n + 2, g⟩ => by
          clear h; exfalso
          replace g := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ g)
          contradiction
        all_goals refine match b with
        | ⟨0, _⟩ => ?_
        | ⟨1, _⟩ => ?_
        | ⟨n + 2, g⟩ => by
          clear h; exfalso
          replace g := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ g)
          contradiction
        rfl
        contradiction
        contradiction
        rfl
      surj' := by
        intro b
        cases b
        exact ⟨⟨0, by decide⟩, rfl⟩
        exact ⟨⟨1, by decide⟩, rfl⟩
    }
    try_decode := .some {
      val
      | false => ⟨0, by decide⟩
      | true => ⟨1, by decide⟩
      property := by
        intro x
        refine match x with
        | ⟨0, _⟩ => ?_
        | ⟨1, _⟩ => ?_
        | ⟨n + 2, g⟩ => by
          exfalso
          replace g := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ g)
          contradiction
        rfl
        rfl
    }
  }

instance instUnique [Subsingleton α] [Inhabited α] : Fintype α where
  card := 1
  repr := Trunc.mk {
    bij := {
      toFun _ := default
      inj' := by
        intro a b h
        match a with
        | ⟨_ + 1, h⟩ => nomatch Nat.lt_of_succ_lt_succ h
        | ⟨0, h⟩ =>
        match b with
        | ⟨_ + 1, h⟩ => nomatch Nat.lt_of_succ_lt_succ h
        | ⟨0, h⟩ =>
        rfl
      surj' := by
        intro
        exists ⟨0, Nat.zero_lt_succ _⟩
        apply Subsingleton.allEq
    }
    try_decode := .some <| {
      val _ := ⟨0, by decide⟩
      property := by
        intro x
        match x with
        | ⟨_ + 1, h⟩ => nomatch Nat.lt_of_succ_lt_succ h
        | ⟨0, h⟩ =>
        rfl
    }
  }

end Fintype
