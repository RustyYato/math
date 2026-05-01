import LeanMath.Data.Bijection.Defs
import LeanMath.Data.Equiv.Basic
import LeanMath.Data.Trunc.Defs
import LeanMath.Tactic.AxiomBlame
import LeanMath.Logic.IsEmpty
import LeanMath.Data.Nat.Find
import LeanMath.Data.POption.Defs
import LeanMath.Data.FinEncodable.Defs

structure Fintype.Repr (α: Sort u) (n: Nat) where
  bij: Fin n ↭ α
  try_decode: POption ({ f: α -> Fin n // Function.LeftInverse f bij })

class Fintype (α: Sort u) : Sort (max u 1) where
  card: Nat
  repr: Trunc (Fintype.Repr α card)

abbrev Finite (α: Sort u) : Prop := Nonempty (Fintype α)
class Infinite (α: Sort u) : Prop where
  protected notFinite: ¬Finite α

def notFinite (α: Sort*) [Infinite α] : ¬Finite α := Infinite.notFinite

instance [Fintype α] : Finite α := ⟨inferInstance⟩

namespace Fintype

@[implicit_reducible]
def Repr.toFinEncodable (r: Fintype.Repr α n) : FinEncodable α where
  card := n
  bij := r.bij
  try_decode := r.try_decode

@[implicit_reducible]
def Repr.ofFinEncodable (α: Sort*) [f: FinEncodable α]: Fintype.Repr α f.card where
  bij := f.bij
  try_decode := f.try_decode

private def toTruncFinEncodable (f: Fintype α) : Trunc (FinEncodable α) :=
  f.repr.map fun r => {
    card := f.card
    bij := r.bij
    try_decode := r.try_decode
  }

def truncFinEncodable : Fintype α ≃ Trunc (FinEncodable α) where
  toFun := toTruncFinEncodable
  invFun x := x.lift (fun x => {
    card := x.card
    repr := Trunc.mk {
      bij := x.bij
      try_decode := x.try_decode
    }
  }) <| by
    intro a b
    dsimp
    suffices h:a.card = b.card by
      obtain ⟨ ⟩ := a
      obtain ⟨ ⟩ := b
      dsimp; subst h
      congr 1; apply Subsingleton.allEq
    apply FinEncodable.card_eq
  leftInv x := by
    induction x with | _ =>
    rfl
  rightInv x := by
    obtain ⟨c, x⟩ := x
    induction x with | _ =>
    rfl

def card_eq_finencodable (α: Sort*) [FinEncodable α] [fa: Fintype α] :
  Fintype.card α = FinEncodable.card α := by
  obtain ⟨ca, fa⟩ := fa
  induction fa with | mk fa =>
  let f : FinEncodable α := {
    card := ca
    bij := fa.bij
    try_decode := fa.try_decode
  }
  show f.card = _
  apply FinEncodable.card_eq

def card_eq (fa fb: Fintype α) : fa.card = fb.card := by
  induction truncFinEncodable fa with | _ =>
  rw [card_eq_finencodable, card_eq_finencodable]

instance : Subsingleton (Fintype α) where
  allEq a b := by
    have card_eq := card_eq a b
    obtain ⟨ca, a⟩ := a
    obtain ⟨cb, b⟩ := b
    cases card_eq
    congr
    apply Subsingleton.allEq

instance [f: FinEncodable α] : Fintype α where
  card := FinEncodable.card α
  repr := Trunc.mk {
    bij := f.bij
    try_decode := f.try_decode
  }

instance : Fintype (Fin n) := inferInstance

def card_fin {f: Fintype (Fin n)} : f.card = n := by
  rw [Fintype.card_eq f instFin]
  rfl

instance : Fintype Bool := inferInstance

def card_bool {f: Fintype Bool} : f.card = 2 := by
  rw [Fintype.card_eq f instBool]
  rfl

instance (priority := 100) instUnique [Subsingleton α] [Inhabited α] : Fintype α :=
  inferInstance

def card_unique [Subsingleton α] [Inhabited α] {f: Fintype α} : f.card = 1 := by
  rw [Fintype.card_eq f instUnique]
  rfl

instance (priority := 100) instIsEmpty [IsEmpty α] : Fintype α :=
  inferInstance

def card_empty [IsEmpty α] {f: Fintype α} : f.card = 0 := by
  rw [Fintype.card_eq f instIsEmpty]
  rfl

@[implicit_reducible]
def ofBij [ft: Fintype α] (f: α ↭ β) : Fintype β where
  card := card α
  repr :=
    ft.repr.map <| fun r => {
      bij := f.comp r.bij
      try_decode := .none
    }

@[implicit_reducible]
def ofList (list: List α) (ha: list.Nodup) (hb: ∀x, x ∈ list) : Fintype α where
  card := list.length
  repr := Trunc.mk {
    try_decode := .none
    bij := {
      toFun i := list[i]
      surj' := by
        intro x
        have ⟨i, h, hi⟩ := List.getElem_of_mem (hb x)
        exists ⟨i, h⟩
      inj' := by
        have hx := ha
        clear ha hb
        intro ⟨a, ha⟩ ⟨b, hb⟩ h
        dsimp at h; congr
        induction list generalizing a b with
        | nil => contradiction
        | cons x xs ih =>
          rcases a with _ | a <;> rcases b with _ | b
          · rfl
          · dsimp at h
            exfalso; apply (List.nodup_cons.mp hx).left
            rw [h]; apply List.getElem_mem
          · dsimp at h
            exfalso; apply (List.nodup_cons.mp hx).left
            rw [←h]; apply List.getElem_mem
          · congr; apply ih
            exact hx.tail
            assumption
            apply Nat.lt_of_succ_lt_succ
            assumption
            apply Nat.lt_of_succ_lt_succ
            assumption
    }
  }

@[implicit_reducible]
def ofEquiv [ft: Fintype α] (f: α ≃ β) : Fintype β where
  card := card α
  repr :=
    ft.repr.map <| fun r =>
    let := r.toFinEncodable
    let := @FinEncodable.ofEquiv _ _ r.toFinEncodable f
    Repr.ofFinEncodable _

instance : Fintype Prop := inferInstance

def card_prop {f: Fintype Prop} : f.card = 2 := by
  rw [Fintype.card_eq f instProp]
  rfl

instance [ft: Fintype ι] : Fintype (POption ι) where
  card := ft.card + 1
  repr :=
    ft.repr.map fun r =>
      let := @FinEncodable.instPOption ι r.toFinEncodable
      let x := Repr.ofFinEncodable (POption ι)
      x

def card_poption {f: Fintype (POption α)} [Fintype α] : f.card = Fintype.card α + 1 := by
  rw [Fintype.card_eq f instPOption]
  rfl

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

def fold_bij {ι ι' α: Sort*} [ft: Fintype ι] {ft': Fintype ι'}
  (bij: ι ↭ ι') (f: ι' -> α -> α)
  (fcomm: ∀i j a, f i (f j a) = f j (f i a)) {acc} :
  fold f fcomm acc = fold (fun i => f (bij i)) (by
    intro i j a
    dsimp; rw [fcomm]) acc := by
    rw [show ft' = ofBij bij from Subsingleton.allEq _ _]
    clear ft'
    obtain ⟨card, ft⟩ := ft
    induction ft with | mk ft =>
    rfl

def finBij (ι: Sort*) [Fintype ι] : Trunc (Fin (card ι) ↭ ι) :=
  Fintype.repr.map fun x => x.bij

def finEquiv (ι: Sort*) [Fintype ι] [DecidableEq ι] : Trunc (Fin (card ι) ≃ ι) :=
  Fintype.repr.map fun repr =>
  repr.toFinEncodable.eqv

def finBijOrEquiv (ι: Sort*) [Fintype ι] : Trunc ((Fin (card ι) ↭ ι) ⊕' (Fin (card ι) ≃ ι)) :=
  Fintype.repr.map fun repr =>
  repr.toFinEncodable.bij_or_eqv

@[simp] def fold_zero (f: Fin 0 -> α -> α) : fold f nofun = id := rfl

@[simp] def fold_succ (f: Fin (n + 1) -> α -> α) (fcomm) :
  fold f fcomm acc = f 0 (fold (fun i: Fin n => f i.succ) (by
    intro i j a; dsimp; rw [fcomm]) acc) := by
  unfold fold
  simp [repr]
  show Fin.foldr (n + 1) _ _ = _
  rw [Fin.foldr_succ]
  rfl

def any [Fintype ι] (f: ι -> Bool) : Bool :=
  fold (fun i acc => acc || f i) (by
    intro i j a
    dsimp
    cases a <;> cases f j <;> cases f i <;> rfl) false

def all [Fintype ι] (f: ι -> Bool) : Bool :=
  !any (fun i => !f i)

private def any_spec' (f: Fin n -> Bool) : any f ↔ ∃i, f i := by
  unfold any
  induction n with
  | zero => simp
  | succ n ih =>
    simp [ih]
    apply Iff.intro
    intro h
    rcases h with ⟨i, hi⟩ | h
    exists i.succ
    exists 0
    intro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => right; assumption
    | succ i => left; exists i

def any_spec [Fintype ι] (f: ι -> Bool) : any f ↔ ∃i, f i := by
  unfold any
  induction finBij ι with | mk g =>
  rw [fold_bij g]
  apply Iff.trans (any_spec' (f ∘ g))
  apply Iff.intro
  · intro ⟨i, hi⟩
    exists g i
  · intro ⟨i, hi⟩
    obtain ⟨i, rfl⟩ := g.surj i
    exists i

def all_spec [Fintype ι] (f: ι -> Bool) : all f ↔ ∀i, f i := by
  unfold all
  simp [←Bool.not_eq_true]
  rw [any_spec]
  apply Iff.trans _ Decidable.not_exists_not
  simp

instance [Fintype α] : Fintype (ULift α) :=
  ofEquiv (Equiv.ulift _)

def card_ulift {f: Fintype (ULift α)} [Fintype α] : f.card = Fintype.card α := by
  rw [Fintype.card_eq f instULift]
  rfl

instance [Fintype α] : Fintype (PLift α) :=
  ofEquiv (Equiv.plift _)

def card_plift {f: Fintype (PLift α)} [Fintype α] : f.card = Fintype.card α := by
  rw [Fintype.card_eq f instPLift]
  rfl

instance [Fintype α] : Fintype (Option α) :=
  ofEquiv Equiv.poption_eq_option

def card_option {f: Fintype (Option α)} [Fintype α] : f.card = Fintype.card α + 1 := by
  rw [Fintype.card_eq f instOption]
  rfl

end Fintype

namespace Finite

@[implicit_reducible]
def ofBij [ft: Finite α] (f: α ↭ β) : Finite β :=
  have ⟨_⟩ := ft
  have := Fintype.ofBij f
  inferInstance

def finBij (ι: Sort*) [ft: Finite ι] : ∃card: ℕ, Nonempty (Fin card ↭ ι) := by
  obtain ⟨ft⟩ := ft
  induction Fintype.finBij ι with | _ x =>
  exists Fintype.card ι
  exact ⟨x⟩

instance [ft: Finite ι] : Finite (POption ι) := by
  obtain ⟨ ⟩ := ft
  infer_instance

instance [ft: Finite ι] : Finite (Option ι) := by
  obtain ⟨ ⟩ := ft
  infer_instance

instance [Finite α] : Finite (ULift α) :=
  ofBij (Equiv.ulift α).toBij

instance [Finite α] : Finite (PLift α) :=
  ofBij (Equiv.plift α).toBij

def induction
  {motive: ∀α: Type u, [Finite α] -> Prop}
  (bij: ∀α β: Type u, [Finite α] -> [Finite β] -> (α ↭ β) -> motive α -> motive β)
  (zero: motive PEmpty)
  (succ: ∀α: Type u, [Finite α] -> motive α -> motive (POption α))
  (α: Type u) (hf: Finite α) : motive α := by
  have ⟨card, ⟨hbij⟩⟩ := finBij α
  apply bij (ULift (Fin card)) α _ _
  exact (Equiv.ulift _).symm.toBij.trans hbij
  clear hbij
  induction card with
  | zero =>
    apply bij PEmpty
    apply Equiv.empty.toBij
    apply zero
  | succ n ih =>
    apply bij (POption (ULift (Fin n)))
    apply Equiv.toBij
    apply Equiv.trans _ (Equiv.ulift_congr.{_, _, u, u} (Equiv.fin_succ_eqv_some_fin.symm))
    exact {
      toFun
      | .none => .up .none
      | .some x => .up (.some x.down)
      invFun
      | .up .none => .none
      | .up (.some x) => .some (.up x)
      leftInv := by intro x; rcases x with x | x <;> rfl
      rightInv := by intro x; rcases x with x | x <;> rfl
    }
    apply succ
    apply ih

@[implicit_reducible]
def ofEmbed [LEM] {β: Type u} [ft: Finite β] (f: α ↪ β) : Finite α := by
  induction β, ft using induction with
  | bij β₀ β₁ bij ih => exact ih (f.trans (Equiv.ofBij bij).symm.toEmbedding)
  | zero =>
    have : IsEmpty α := { elim x := elim_empty (f x) }
    infer_instance
  | succ β ih =>
    rcases em (Function.Surjective f) with hf | hf
    · have : α ↭ POption β := {
        toFun := f
        inj' := f.inj
        surj' := hf
      }
      apply ofBij ((Equiv.ofBij this).symm.toBij)
    · replace hf := LEM.not_forall.mp hf
      simp at hf
      obtain ⟨x, hx⟩ := hf
      open UniqueChoice in
      let f' := f.trans (Equiv.swap .none x (Equiv.id _)).toEmbedding
      have hf' (a: α) : (f' a) ≠ .none := by
        intro h
        replace h : (Equiv.swap _ _ (Equiv.id _)) (f a) = _ := h
        rw [←Equiv.symm_eq_iff] at h
        simp [Equiv.symm_swap, Equiv.apply_swap] at h
        nomatch hx _ h.symm
      apply ih
      exact {
        toFun x := POption.get (f' x) (hf' _)
        inj := by
          intro x y h
          dsimp at h
          exact f'.inj (POption.get_inj.mp h)
      }

end Finite

namespace Fintype

instance [Fintype ι] {P: ι -> Prop} [DecidablePred P] : Decidable (∃x, P x) :=
  decidable_of_bool (any (fun i => decide (P i))) <| by simp [any_spec]

instance [Fintype ι] {P: ι -> Prop} [DecidablePred P] : Decidable (∀x, P x) :=
  decidable_of_iff _  Decidable.not_exists_not

private def is_inr : α ⊕' β -> Bool
| .inl _ => false
| .inr _ => true

def factorBijOrEquiv {ι: Sort*} {α: ι -> Sort*} [Fintype ι] [∀i, Fintype (α i)] (
  f: ∀i, (Fin (card (α i)) ↭ α i) ⊕' Fin (card (α i)) ≃ α i
) : (∀i, Fin (card (α i)) ↭ α i) ⊕' (∀i, Fin (card (α i)) ≃ α i) :=
  if hf:∀i, is_inr (f i) then
    .inr (fun i => match h:(f i) with
      | .inr x => x
      | .inl _ => nomatch h ▸ (hf i))
  else
    .inl (fun i => match f i with
      | .inl x => x
      | .inr x => x.toBij)

end Fintype

namespace Finite

instance (priority := 900) [Finite ι] {P: ι -> Prop} [ExcludedMiddlePred P] : ExcludedMiddle (∃x, P x) where
  em := by
    have ⟨card, ⟨bij⟩⟩ := Finite.finBij ι
    rcases em (∃i, P (bij i)) with ⟨i, h⟩ | h
    · left; exists bij i
    · right; intro g; apply h
      obtain ⟨i, hi⟩ := g
      obtain ⟨n, rfl⟩ := bij.surj i
      exists n

instance (priority := 900) [Finite ι] {P: ι -> Prop} [ExcludedMiddlePred P] : ExcludedMiddle (∀x, P x) :=
  inferInstance

end Finite

namespace Infinite

@[implicit_reducible]
def ofBij [Infinite β] (f: α ↭ β) : Infinite α where
  notFinite := by
    intro h;
    apply notFinite β
    apply Finite.ofBij f

@[implicit_reducible]
def ofEmbed [Infinite α] [LEM] (f: α ↪ β) : Infinite β where
  notFinite := by
    intro h;
    apply notFinite α
    apply Finite.ofEmbed (β := PLift β)
    apply f.trans
    apply (Equiv.plift _).toEmbedding

instance [Infinite α] : Infinite (ULift α) :=
  ofBij (Equiv.ulift _).symm.toBij
instance [Infinite α] : Infinite (PLift α) :=
  ofBij (Equiv.plift _).symm.toBij

end Infinite
