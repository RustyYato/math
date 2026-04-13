import LeanMath.Data.Equiv.Basic
import LeanMath.Tactic.PPWithUniv

@[pp_with_univ]
inductive ZFSet.Pre : Type u where
| intro (ι: Sort u) (mem: ι -> ZFSet.Pre)

@[pp_with_univ]
inductive ZFSet.Pre.Equiv : ZFSet.Pre -> ZFSet.Pre -> Prop where
| intro (ι₀: Sort u) (ι₁: Sort u)
  (mem₀: ι₀ -> ZFSet.Pre) (mem₁: ι₁ -> ZFSet.Pre)
  (f: ι₀ ≃ ι₁) : (∀(i₀: ι₀), Equiv (mem₀ i₀) (mem₁ (f i₀))) ->
  Equiv (.intro ι₀ mem₀) (.intro ι₁ mem₁)

@[pp_with_univ]
inductive ZFSet.Pre.Mem : ZFSet.Pre -> ZFSet.Pre -> Prop where
| intro (ι: Sort u) (mem: ι -> ZFSet.Pre) (i: ι) (x: ZFSet.Pre) :
  ZFSet.Pre.Equiv (mem i) x -> ZFSet.Pre.Mem (.intro ι mem) x

def ZFSet.Pre.Equiv.refl (s: ZFSet.Pre) : Pre.Equiv s s := by
  induction s with
  | intro ι mem ih =>
  refine Pre.Equiv.intro ι ι mem mem (Equiv.id _) ?_
  assumption

def ZFSet.Pre.Equiv.symm {s t: ZFSet.Pre} : Pre.Equiv s t -> Pre.Equiv t s := by
  intro h
  induction h with
  | intro ι₀ ι₁ mem₀ mem₁ f h ih =>
  refine Pre.Equiv.intro ι₁ ι₀ mem₁ mem₀ f.symm ?_
  intro i
  have := ih (f.symm i)
  rwa [Equiv.symm_coe] at this

def ZFSet.Pre.Equiv.trans {s t u: ZFSet.Pre} : Pre.Equiv s t -> Pre.Equiv t u -> Pre.Equiv s u := by
  intro h g
  induction h generalizing u with
  | intro ι₀ ι₁ mem₀ mem₁ hf h ih =>
  cases g with
  | intro ι₁ ι₂ mem₁ mem₂ gf g =>
  refine Pre.Equiv.intro ι₀ ι₂ mem₀ mem₂ (hf.trans gf) ?_
  intro i
  apply ih
  apply g

instance ZFSet.Pre.setoid : Setoid ZFSet.Pre where
  r := ZFSet.Pre.Equiv
  iseqv := {
    refl := ZFSet.Pre.Equiv.refl
    symm := ZFSet.Pre.Equiv.symm
    trans := ZFSet.Pre.Equiv.trans
  }

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

end ZFSet
