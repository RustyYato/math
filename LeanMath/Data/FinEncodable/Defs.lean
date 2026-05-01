import LeanMath.Data.Bijection.Defs
import LeanMath.Data.Equiv.Basic
import LeanMath.Data.Trunc.Defs
import LeanMath.Tactic.AxiomBlame
import LeanMath.Logic.IsEmpty
import LeanMath.Data.Nat.Find
import LeanMath.Data.POption.Defs

class FinEncodable (α: Sort u) where
  card: ℕ
  bij: Fin card ↭ α
  try_decode: POption ({ f: α -> Fin card // Function.LeftInverse f bij })

namespace FinEncodable

instance : FinEncodable (Fin n) where
  card := n
  bij := Bijection.id _
  try_decode := .some ⟨id, by intro; rfl⟩

private def cases_fin2 (motive: Fin 2 -> Sort u)
  (zero: motive ⟨0, by decide⟩)
  (one: motive ⟨1, by decide⟩) (x: Fin 2) : motive x :=
  match x with
  | ⟨0, _⟩ => zero
  | ⟨1, _⟩ => one
  | ⟨n + 2, g⟩ => by
    nomatch Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ g)

instance : FinEncodable Bool where
  card := 2
  bij := {
    toFun
    | ⟨0, _⟩ => false
    | ⟨1, _⟩ => true
    | ⟨n + 2, h⟩ => by
      replace h := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h)
      contradiction
    inj' := by
      intro a b h
      cases a using cases_fin2 <;>
      cases b using cases_fin2
      any_goals rfl
      all_goals contradiction
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
      cases x using cases_fin2
      rfl
      rfl
  }

instance (priority := 100) instUnique [Subsingleton α] [Inhabited α] : FinEncodable α where
  card := 1
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

instance (priority := 100) [IsEmpty α] : FinEncodable α where
  card := 0
  bij := {
    toFun := elim_empty
    inj' := rec_elim_empty
    surj' := rec_elim_empty
  }
  try_decode := .some <| {
    val := rec_elim_empty
    property := rec_elim_empty
  }

@[implicit_reducible]
def ofBij [ft: FinEncodable α] (f: α ↭ β) : FinEncodable β where
  card := card α
  bij := f.comp ft.bij
  try_decode := .none

@[implicit_reducible]
def ofEquiv [ft: FinEncodable α] (f: α ≃ β) : FinEncodable β where
  card := card α
  bij := f.toBij.comp ft.bij
  try_decode :=
    match ft.try_decode with
    | .none => .none
    | .some d => .some {
      val b := d.val (f.symm b)
      property := by
        intro x
        dsimp
        show d.val (f.symm (f _)) = _
        rw [f.coe_symm, d.property]
    }

instance : FinEncodable Prop :=
  ofBij (α := Bool) {
    toFun b := b
    inj' := by
      intro a b h
      cases a <;> cases b
      rfl; contradiction
      contradiction; rfl
    surj' := by
      intro P
      by_cases P
      exists true
      simpa
      exists false
      simpa
  }

instance instPOption [ft: FinEncodable ι] : FinEncodable (POption ι) where
  card := card ι + 1
  bij := Bijection.finsucc_poption ft.bij
  try_decode := ft.try_decode.map fun r => {
    val
    | .some x => (r.val x).succ
    | .none => ⟨0, Nat.zero_lt_succ _⟩
    property := by
      intro x; dsimp
      cases x using Fin.cases
      rw [Bijection.apply_finsucc_poption_zero]
      rw [Bijection.apply_finsucc_poption_succ]
      dsimp; congr; apply r.property
  }

instance [FinEncodable α] : FinEncodable (ULift α) :=
  ofEquiv (Equiv.ulift _)

instance [FinEncodable α] : FinEncodable (PLift α) :=
  ofEquiv (Equiv.plift _)

instance [FinEncodable α] : FinEncodable (Option α) :=
  ofEquiv Equiv.poption_eq_option

def fold {ι α: Sort*} [ft: FinEncodable ι] (f: ι -> α -> α) : α -> α :=
  Fin.foldr ft.card (fun i => f (ft.bij i))

@[simp] def fold_zero (f: Fin 0 -> α -> α) : fold f = id := rfl

@[simp] def fold_succ (f: Fin (n + 1) -> α -> α) :
  fold f acc = f 0 (fold (fun i: Fin n => f i.succ) acc) := by
  show Fin.foldr (n + 1) _ _ = _
  rw [Fin.foldr_succ]
  rfl

def bij_or_eqv (ι: Sort*) [repr: FinEncodable ι] : (Fin (card ι) ↭ ι) ⊕' (Fin (card ι) ≃ ι) :=
  match repr.try_decode with
  | .some ⟨invFun, invFun_spec⟩ =>
    .inr {
      toFun := repr.bij
      invFun := invFun
      rightInv := invFun_spec
      leftInv := by
        intro x
        obtain ⟨i, rfl⟩ := repr.bij.surj x
        rw [invFun_spec i]
    }
  | .none =>
    let card :=  repr.card
    have spec (x: ι) : ∃(n: ℕ) (hn: n < card), x = repr.bij ⟨n, hn⟩ := by
      have ⟨i, hi⟩ := repr.bij.surj x
      refine ⟨_, i.isLt, hi.symm⟩
    .inl repr.bij

def eqv (ι: Sort*) [repr: FinEncodable ι] [DecidableEq ι] : Fin (card ι) ≃ ι :=
  match repr.try_decode with
  | .some ⟨invFun, invFun_spec⟩ =>
    {
      toFun := repr.bij
      invFun := invFun
      rightInv := invFun_spec
      leftInv := by
        intro x
        obtain ⟨i, rfl⟩ := repr.bij.surj x
        rw [invFun_spec i]
    }
  | .none =>
    let card := repr.card
    have spec (x: ι) : ∃(n: ℕ) (hn: n < card), x = repr.bij ⟨n, hn⟩ := by
      have ⟨i, hi⟩ := repr.bij.surj x
      refine ⟨_, i.isLt, hi.symm⟩
    {
      toFun := repr.bij
      invFun x := {
        val := Nat.find (spec x)
        isLt := (Nat.find_spec (spec x)).1
      }
      leftInv := by
        intro x
        obtain ⟨hn, h⟩ := Nat.find_spec (spec x)
        exact h.symm
      rightInv := by
        intro i
        apply repr.bij.inj
        dsimp
        have ⟨_, h⟩ := Nat.find_spec (spec (repr.bij i))
        exact h.symm
    }

def card_le (fa: FinEncodable α) (fb: FinEncodable β) (f: α ↪ β) : fa.card ≤ fb.card := by
  obtain ⟨ca, fa, ga⟩ := fa
  obtain ⟨cb, fb, gb⟩ := fb
  show ca ≤ cb
  clear ga gb
  obtain ⟨fa, fainj, fasurj⟩ := fa
  obtain ⟨fb, fbinj, fbsurj⟩ := fb
  have eqv : ∀a: α, (∃i, fa i = a) ↔ (∃i, fb i = f a) := by
    intro a
    apply Iff.intro <;> intro
    apply fbsurj
    apply fasurj
  clear fasurj fbsurj
  induction ca generalizing cb with
  | zero => apply Nat.zero_le
  | succ ca ih =>
    have ⟨i, hi⟩ := (eqv (fa ⟨0, Nat.zero_lt_succ _⟩)).mp ⟨_, rfl⟩
    replace hi := hi.symm
    cases cb with
    | zero => exact i.elim0
    | succ cb =>
      apply Nat.succ_le_succ
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
                rw [←inj f hy] at hx
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
        · intro ⟨x, hx⟩; dsimp
          have ⟨y, hy⟩ := (eqv a).mpr ⟨_, hx⟩
          rw [←hy] at hx
          match y with
          | ⟨0, _⟩ =>
            rw [hi] at hx
            replace hx := fbinj hx
            split at hx
            · rename_i g
              rw [←hx] at g
              dsimp at g
              nomatch Nat.lt_irrefl _ g
            · rename_i g
              rw [←hx] at g
              exfalso; apply g
              apply Nat.lt_succ_self
          | ⟨y + 1, hy⟩ =>
            exists ⟨y, ?_⟩
            apply Nat.lt_of_succ_lt_succ
            assumption
            assumption

def card_eq (fa fb: FinEncodable α) : fa.card = fb.card := by
  apply Nat.le_antisymm
  apply card_le _ _ (Embedding.id _)
  apply card_le _ _ (Embedding.id _)

end FinEncodable
