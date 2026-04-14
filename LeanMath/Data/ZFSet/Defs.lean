import LeanMath.Data.Equiv.Basic
import LeanMath.Tactic.PPWithUniv

@[pp_with_univ]
inductive ZFSet.Pre : Type (u + 1) where
| intro (ι: Type u) (mem: ι -> ZFSet.Pre)

def ZFSet.Pre.«Type» : ZFSet.Pre.{u} -> Type u
| .intro ι _ => ι

@[coe]
def ZFSet.Pre.Mem : ∀s: ZFSet.Pre, s.Type -> ZFSet.Pre
| .intro _ mem => mem

@[simp] def ZFSet.Pre.mk_Type (ι: Type u) (mem: ι -> ZFSet.Pre) :  (intro ι mem).Type = ι := rfl
@[simp] def ZFSet.Pre.mk_Mem (ι: Type u) (mem: ι -> ZFSet.Pre) :  (intro ι mem).Mem = mem := rfl

inductive ZFSet.EquivState.{u} where
| intro (a b: ZFSet.Pre.{u})
| exists_left (a b: ZFSet.Pre.{u}) (a₀: a.Type)
| exists_right (a b: ZFSet.Pre.{u}) (b₀: b.Type)

inductive ZFSet.PreEquiv : ZFSet.EquivState.{u} -> Prop where
| intro (a b: ZFSet.Pre.{u}) :
  (∀a₀, PreEquiv (.exists_left a b a₀)) ->
  (∀b₀, PreEquiv (.exists_right a b b₀)) ->
  PreEquiv (.intro a b)
| equiv_left (a b: ZFSet.Pre.{u}) (a₀: a.Type) (b₀: b.Type) :
  PreEquiv (.intro (a.Mem a₀) (b.Mem b₀)) ->
  PreEquiv (.exists_left a b a₀)
| equiv_right (a b: ZFSet.Pre.{u}) (a₀: a.Type) (b₀: b.Type) :
  PreEquiv (.intro (a.Mem a₀) (b.Mem b₀)) ->
  PreEquiv (.exists_right a b b₀)

instance : HasEquiv ZFSet.Pre.{u} where
  Equiv a b := ZFSet.PreEquiv (.intro a b)

def ZFSet.Pre.Equiv.intro
  (a b: ZFSet.Pre.{u})
  (hfwd: ∀i: a.Type, ∃j: b.Type, a.Mem i ≈ b.Mem j)
  (hrev: ∀j: b.Type, ∃i: a.Type, a.Mem i ≈ b.Mem j) :
  a ≈ b := by
  cases a with | _ a amem =>
  cases b with | _ b bmem =>
  apply ZFSet.PreEquiv.intro
  · intro i
    have ⟨j, h⟩ := hfwd i
    apply PreEquiv.equiv_left
    apply h
  · intro j
    have ⟨i, h⟩ := hrev j
    apply PreEquiv.equiv_right
    apply h

@[induction_eliminator]
def ZFSet.Pre.Equiv.rec {motive: ∀a b: ZFSet.Pre, a ≈ b -> Prop}
  (intro: ∀(a b: ZFSet.Pre)
    (hfwd: ∀i: a.Type, ∃(j: b.Type) (h: a.Mem i ≈ b.Mem j), motive _ _ h)
    (hrev: ∀j: b.Type, ∃(i: a.Type) (h: a.Mem i ≈ b.Mem j), motive _ _ h),
    motive a b (ZFSet.Pre.Equiv.intro a b (by
      intro i; have ⟨j, h, _⟩ := hfwd i; exists j) (by
      intro i; have ⟨j, h, _⟩ := hrev i; exists j)))
  {a b: ZFSet.Pre} (h: a ≈ b) : motive a b h := by
  have ab: ZFSet.PreEquiv _ := h
  show motive a b ab
  induction a generalizing b with | _ α αmem ih =>
  cases b with | _ β βmem =>
  cases ab with | _ _ _ fwd rev =>
  dsimp at fwd rev
  apply intro <;> dsimp
  · intro i
    cases fwd i with | _ _ _ _ j =>
    refine ⟨j, ?_, ?_⟩
    assumption
    apply ih
    assumption
  · intro i
    cases rev i with | _ _ _ j =>
    refine ⟨j, ?_, ?_⟩
    assumption
    apply ih
    assumption

@[cases_eliminator]
def ZFSet.Pre.Equiv.cases {motive: ∀a b: ZFSet.Pre, a ≈ b -> Prop}
  (intro: ∀(a b: ZFSet.Pre)
    (fwd: ∀i: a.Type, ∃(j: b.Type), a.Mem i ≈ b.Mem j)
    (rev: ∀j: b.Type, ∃(i: a.Type), a.Mem i ≈ b.Mem j),
    motive a b (ZFSet.Pre.Equiv.intro a b fwd rev))
  {a b: ZFSet.Pre} (h: a ≈ b) : motive a b h := by
  induction h with | _ a b fwd rev =>
  apply intro
  intro i; have ⟨j, _, _⟩ := fwd i; exists j
  intro i; have ⟨j, _, _⟩ := rev i; exists j

def ZFSet.PreEquiv.fwd
  {a b: ZFSet.Pre} (h: a ≈ b) : ∀i: a.Type, ∃(j: b.Type), a.Mem i ≈ b.Mem j := by
  cases h
  assumption
def ZFSet.PreEquiv.rev
  {a b: ZFSet.Pre} (h: a ≈ b) : ∀j: b.Type, ∃(i: a.Type), a.Mem i ≈ b.Mem j := by
  cases h
  assumption

@[refl]
def ZFSet.Pre.Equiv.refl (s: ZFSet.Pre) : s ≈ s := by
  induction s with
  | intro ι mem ih =>
  apply Pre.Equiv.intro
  iterate 2
  intro i; exists i; apply ih

@[symm]
def ZFSet.Pre.Equiv.symm {s t: ZFSet.Pre} : s ≈ t -> t ≈ s := by
  intro h
  induction h with
  | intro a b fwd rev =>
  apply intro
  intro i; have ⟨j, h, _⟩ := rev i; exists j
  intro i; have ⟨j, h, _⟩ := fwd i; exists j

def ZFSet.Pre.Equiv.trans {s t u: ZFSet.Pre} : s ≈ t -> t ≈ u -> s ≈ u := by
  intro h g
  induction h generalizing u with
  | intro a b fwd₀ rev₀ =>
  cases g with
  | intro _ c fwd₁ rev₁ =>
  apply intro
  · intro i
    have ⟨j, hj, ih⟩ := fwd₀ i
    have ⟨k, hk⟩ := fwd₁ j
    exists k
    apply ih
    assumption
  · intro i
    have ⟨k, hk⟩ := rev₁ i
    have ⟨j, hj, ih⟩ := rev₀ k
    exists j
    apply ih
    assumption

instance ZFSet.Pre.setoid : Setoid ZFSet.Pre where
  r a b := a ≈ b
  iseqv := {
    refl := ZFSet.Pre.Equiv.refl
    symm := ZFSet.Pre.Equiv.symm
    trans := ZFSet.Pre.Equiv.trans
  }

@[refl]
def ZFSet.Pre.Equiv.refl' (s: ZFSet.Pre) : instHasEquivOfSetoid.Equiv s s := by
  apply ZFSet.Pre.Equiv.refl

@[pp_with_univ]
structure ZFSet.{u} where
  ofQuot :: toQuot : Quotient ZFSet.Pre.setoid.{u}

namespace ZFSet

def ofPre : ZFSet.Pre -> ZFSet := ZFSet.ofQuot ∘ Quotient.mk _

@[induction_eliminator]
def ind {motive: ZFSet -> Prop} (ofPre: ∀a: ZFSet.Pre, motive (ofPre a)) : ∀s, motive s := by
  intro ⟨s⟩; induction s using Quotient.ind with | _ s =>
  apply ofPre

def sound {a b: ZFSet.Pre} : a ≈ b -> ofPre a = ofPre b := by
  intro h
  unfold ofPre
  dsimp; rw [Quotient.sound h]

def exact {a b: ZFSet.Pre} : ofPre a = ofPre b -> a ≈ b := by
  intro h
  exact Quotient.exact (ZFSet.ofQuot.inj h)

def lift (f: ZFSet.Pre -> α) (h: ∀a b, a ≈ b -> f a = f b) (a: ZFSet) : α := a.toQuot.liftOn f h
def lift₂ (f: ZFSet.Pre -> ZFSet.Pre -> α) (h: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: ZFSet) : α := a.toQuot.liftOn₂ b.toQuot f h

instance : Membership Pre Pre where
  mem s t := ∃i, s.Mem i ≈ t

instance : Membership ZFSet ZFSet where
  mem := lift₂ Membership.mem <| by
    suffices ∀a b c d: Pre, a ≈ c -> b ≈ d -> b ∈ a -> d ∈ c by
      intro a b c d h g
      apply propext; apply Iff.intro
      apply this; assumption; assumption
      apply this; symm; assumption; symm; assumption
    intro a b c d ac bd h
    obtain ⟨i, h⟩ := h
    have ⟨j, ac⟩ := ac.fwd i
    exists j
    apply Pre.Equiv.trans _ bd
    apply Pre.Equiv.trans _ h
    symm; assumption

instance : HasSubset ZFSet where
  Subset a b := ∀x, x ∈ a -> x ∈ b

@[ext] def ext (a b: ZFSet) (h: ∀x, x ∈ a ↔ x ∈ b) : a = b := by
  induction a with | _ a =>
  induction b with | _ b =>
  replace h : ∀x, x ∈ a ↔ x ∈ b := fun x => h (ofPre x)
  cases a with | _ a fa =>
  cases b with | _ b fb =>
  apply sound;
  apply Pre.Equiv.intro
  · intro i
    have ⟨j, hj⟩ := (h (fa i)).mp ⟨i, by dsimp; apply Pre.Equiv.refl⟩
    exists j
    symm; assumption
  · intro i
    have ⟨j, hj⟩ := (h (fb i)).mpr ⟨i, by dsimp; apply Pre.Equiv.refl⟩
    exists j

end ZFSet
