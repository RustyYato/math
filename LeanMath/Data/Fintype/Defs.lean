import LeanMath.Data.Bijection.Defs
import LeanMath.Data.Equiv.Defs
import LeanMath.Data.Trunc.Defs
import LeanMath.Tactic.AxiomBlame
import LeanMath.Logic.IsEmpty

inductive POption (α: Sort u) where
| some (a: α)
| none

structure Fintype.Repr (α: Sort u) (n: Nat) where
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

private def cases_fin2 (motive: Fin 2 -> Sort u)
  (zero: motive ⟨0, by decide⟩)
  (one: motive ⟨1, by decide⟩) (x: Fin 2) : motive x :=
  match x with
  | ⟨0, _⟩ => zero
  | ⟨1, _⟩ => one
  | ⟨n + 2, g⟩ => by
    nomatch Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ g)

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
  }

instance (priority := 100) instUnique [Subsingleton α] [Inhabited α] : Fintype α where
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

instance (priority := 100) [IsEmpty α] : Fintype α where
  card := 0
  repr := Trunc.mk {
    bij := {
      toFun := elim_empty
      inj' := rec_elim_empty
      surj' := rec_elim_empty
    }
    try_decode := .some <| {
      val := rec_elim_empty
      property := rec_elim_empty
    }
  }

def ofBij [ft: Fintype α] (f: α ↭ β) : Fintype β where
  card := card α
  repr :=
    ft.repr.map <| fun r => {
      bij := f.comp r.bij
      try_decode := .none
    }

def ofEquiv [ft: Fintype α] (f: α ≃ β) : Fintype β where
  card := card α
  repr :=
    ft.repr.map <| fun r => {
      bij := f.toBij.comp r.bij
      try_decode :=
        match r.try_decode with
        | .none => .none
        | .some d => .some {
          val b := d.val (f.symm b)
          property := by
            intro x
            dsimp
            show d.val (f.symm (f _)) = _
            rw [f.coe_symm, d.property]
        }
    }

instance : Fintype Prop :=
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

def fin_foldr_eq_list_foldr
  {ι α: Type*}
  (f: ι -> α -> α)
  (map: Fin n -> ι)
  (acc: α): Fin.foldr n (fun i => f (map i)) acc = (List.ofFn map).foldr f acc := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Fin.foldr_succ, List.ofFn_succ, List.foldr_cons, ih]

private def fin_foldr_map_eqv
  {ι α β: Sort*}
  (f: ι -> α -> α)
  (eqv: β ≃ α)
  (map: Fin n -> ι)
  (acc: α):
  Fin.foldr n (fun i a => f (map i) a) acc =
  eqv (Fin.foldr n (fun i b => eqv.symm <| f (map i) (eqv b)) (eqv.symm acc)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.foldr_succ, ih]

private def list_perm_of_nodup
  {ι: Type*}
  (as bs: List ι)
  (has: as.Nodup)
  (hbs: bs.Nodup)
  (eqv: ∀i, i ∈ as ↔ i ∈ bs) :
  as ≈ bs := by
  induction has generalizing bs with
  | nil =>
    cases bs with
    | nil => apply List.Perm.refl
    | cons b bs => nomatch (eqv b).mpr (by simp)
  | @cons a as head tail ih =>
    obtain ⟨bs₀, bs₁, rfl⟩ := List.mem_iff_append.mp ((eqv a).mp (by simp))
    apply flip List.Perm.trans
    apply List.perm_append_comm
    apply List.Perm.cons
    rw [List.nodup_append, List.nodup_cons] at hbs
    obtain ⟨hbs₀, ⟨hbs₁, hbs₂⟩, hbs₃⟩ := hbs
    apply ih
    show (bs₁ ++ bs₀).Nodup
    rw [List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    assumption
    assumption
    intro i hi j hj rfl
    have := hbs₃ i hj i (by simp [hi])
    contradiction
    simp
    intro i
    apply Iff.intro
    intro hi
    have := (eqv i).mp (.tail _ hi)
    simp at this
    rcases this with _ | rfl | _
    right; assumption
    nomatch head i hi
    left; assumption
    intro h
    rcases h with h | h
    all_goals
      have g := (eqv i).mpr (by simp [h])
      simp at g
      rcases g with rfl | g
    contradiction
    assumption
    nomatch hbs₃ i h i (by simp)
    assumption

private def list_foldr_eq
  {ι α: Type*}
  (f: ι -> α -> α)
  (as bs: List ι)
  (has: as.Nodup)
  (hbs: bs.Nodup)
  (eqv: ∀i, i ∈ as ↔ i ∈ bs)
  (fcomm: ∀i j a, f i (f j a) = f j (f i a))
  (acc: α):
  as.foldr f acc = bs.foldr f acc := by
  have := list_perm_of_nodup as bs has hbs eqv
  clear eqv has hbs
  induction this with
  | nil => rfl
  | trans _ _ iha ihb  => rw [iha, ihb]
  | cons => simp; congr
  | swap => simp; apply fcomm

private def fin_foldr_eq
  {ι α: Sort*}
  (f: ι -> α -> α)
  (map₀ map₁: Fin n ↭ ι)
  (fcomm: ∀i j a, f i (f j a) = f j (f i a)) :
  Fin.foldr n (fun i => f (map₀ i)) = Fin.foldr n (fun i => f (map₁ i)) := by
  ext acc
  show Fin.foldr _ (fun i a => f ((Equiv.plift _).symm <| (Equiv.plift _ ∘ map₀) i) a) _ =
     Fin.foldr _ (fun i a => f ((Equiv.plift _).symm <| (Equiv.plift _ ∘ map₁) i) a) _
  rw [fin_foldr_map_eqv (eqv := (Equiv.plift _).symm),
    fin_foldr_map_eqv (eqv := (Equiv.plift α).symm)]
  congr 1; simp
  apply Eq.trans _ (fin_foldr_eq_list_foldr
      (ι := PLift ι)
      (α := PLift α)
      (f := fun i a => (Equiv.plift _) <| f ((Equiv.plift _).symm i) ((Equiv.plift _).symm a))
      (map := Equiv.plift _ ∘ map₁)
      (acc := Equiv.plift _ acc)).symm
  apply Eq.trans (fin_foldr_eq_list_foldr
      (ι := PLift ι)
      (α := PLift α)
      (f := fun i a => (Equiv.plift _) <| f ((Equiv.plift _).symm i) ((Equiv.plift _).symm a))
      (map := Equiv.plift _ ∘ map₀)
      (acc := Equiv.plift _ acc))
  apply list_foldr_eq
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj h
    simp
    intro g
    cases Fin.mk.inj (map₀.inj (Equiv.inj _ g))
    exact Nat.lt_irrefl _ h
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj h
    simp
    intro g
    cases Fin.mk.inj (map₁.inj (Equiv.inj _ g))
    exact Nat.lt_irrefl _ h
  · intro i; apply Iff.intro <;> intro
    simp; apply ((Equiv.toBij (Equiv.plift _)).comp map₁).surj
    simp; apply ((Equiv.toBij (Equiv.plift _)).comp map₀).surj
  · intro i j acc
    simp; rw [fcomm]

def fold {ι α: Sort*} [ft: Fintype ι] (f: ι -> α -> α) (fcomm: ∀i j a, f i (f j a) = f j (f i a)) : α -> α :=
  ft.repr.lift (fun repr => Fin.foldr ft.card (fun i => f (repr.bij i))) <| by
    intro a b
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    show Fin.foldr _ (fun i => f (a i)) = Fin.foldr _ (fun i => f (b i))
    apply fin_foldr_eq f a b
    assumption

end Fintype
