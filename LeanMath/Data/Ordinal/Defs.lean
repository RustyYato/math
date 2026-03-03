import LeanMath.Tactic.PPWithUniv
import LeanMath.Tactic.AxiomBlame
import LeanMath.Logic.Relation.Segments
import LeanMath.Order.Defs
import LeanMath.Data.Equiv.Basic

@[pp_with_univ]
structure Ordinal.Pre.{u} where
  ty: Type u
  rel: ty -> ty -> Prop
  [wo: Relation.IsWellOrder rel]

instance : CoeSort Ordinal.Pre.{u} (Type u) where
  coe x := x.ty

instance (p: Ordinal.Pre) : Relation.IsWellOrder p.rel := p.wo

@[pp_with_univ]
inductive Ordinal.Rel.{u, v} : Pre.{u} -> Pre.{v} -> Prop where
| intro {a: Pre.{u}} {b: Pre.{v}} : a.rel ≃r b.rel -> Rel a b


infixr:80 " ≈p " => Ordinal.Rel

namespace Ordinal.Rel

def refl (a: Pre.{u}) : a ≈p a := Rel.intro (RelEquiv.id _)
def symm {a: Pre.{u}} {b: Pre.{v}} : a ≈p b -> b ≈p a
| .intro h => .intro h.symm
def trans {a: Pre.{u}} {b: Pre.{v}} {c: Pre.{v}} : a ≈p b -> b ≈p c -> a ≈p c
| .intro h, .intro g => .intro (g.comp h)

end Ordinal.Rel

instance : Relation.IsRefl Ordinal.Rel where
  refl := Ordinal.Rel.refl
instance : Relation.IsSymm Ordinal.Rel where
  symm := Ordinal.Rel.symm
instance : Relation.IsTrans Ordinal.Rel where
  trans := Ordinal.Rel.trans

instance Ordinal.setoid : Setoid Ordinal.Pre := Relation.setoid Ordinal.Rel

@[pp_with_univ]
structure Ordinal where
  ofQuot :: toQuot : Quotient Ordinal.setoid

namespace Ordinal

def type (rel: α -> α -> Prop) [Relation.IsWellOrder rel] : Ordinal where
  toQuot := Quotient.mk _ {
    ty := _
    rel := rel
  }

def lift (f: ∀{α: Type u} (r: α -> α -> Prop) [Relation.IsWellOrder r], A)
  (h: ∀{α β: Type u} (r: α -> α -> Prop) (s: β -> β -> Prop)
    [Relation.IsWellOrder r] [Relation.IsWellOrder s],
    r ≃r s -> f r = f s)
  (a: Ordinal) : A :=
  Quotient.liftOn a.toQuot (fun p => f p.rel) fun a b h => by
    obtain ⟨eq⟩ := h
    exact h a.rel b.rel eq

def lift₂ (f: ∀{α: Type u}{β: Type v} (r: α -> α -> Prop) (s: β -> β -> Prop) [Relation.IsWellOrder r] [Relation.IsWellOrder s], A)
  (h: ∀{α₀ β₀: Type u} {α₁ β₁: Type v} (r₀: α₀ -> α₀ -> Prop) (r₁: α₁ -> α₁ -> Prop) (s₀: β₀ -> β₀ -> Prop) (s₁: β₁ -> β₁ -> Prop)
    [Relation.IsWellOrder r₀] [Relation.IsWellOrder r₁] [Relation.IsWellOrder s₀] [Relation.IsWellOrder s₁],
    r₀ ≃r s₀ -> r₁ ≃r s₁ -> f r₀ r₁ = f s₀ s₁)
  (a: Ordinal.{u}) (b: Ordinal.{v}) : A :=
  Quotient.liftOn₂ a.toQuot b.toQuot (fun a b => f a.rel b.rel) fun a b c d h₀ h₁ => by
    obtain ⟨h₀⟩ := h₀
    obtain ⟨h₁⟩ := h₁
    apply h
    exact h₀
    exact h₁

@[simp] def lift_type (r: α -> α -> Prop) [Relation.IsWellOrder r] : lift f h (type r) = f r := rfl
@[simp] def lift₂_type (r: α -> α -> Prop) (s: β -> β -> Prop) [Relation.IsWellOrder r] [Relation.IsWellOrder s] : lift₂ f h (type r) (type s) = f r s := rfl

@[local induction_eliminator]
def ind {motive: Ordinal -> Prop} (type: ∀{α} (r: α -> α -> Prop) [Relation.IsWellOrder r], motive (type r)) : ∀o, motive o := by
  intro ⟨o⟩
  induction o using Quotient.ind with | _ o =>
  apply type

def sound {r: α -> α -> Prop} {s: β -> β -> Prop} [Relation.IsWellOrder r] [Relation.IsWellOrder s] : r ≃r s -> type r = type s := by
  intro h
  unfold type; congr 1
  apply Quotient.sound
  exact ⟨h⟩

instance : LE Ordinal where
  le := lift₂ (fun r s => Nonempty (r ≼r s)) <| by
    intro α₀ β₀ α₁ β₁ r₀ r₁ s₀ s₁ _ _ _ _ h₀ h₁
    simp
    apply Iff.intro
    · intro ⟨f⟩
      exact ⟨h₀.symm.toInitialSegment.trans (f.trans h₁.toInitialSegment)⟩
    · intro ⟨f⟩
      exact ⟨h₀.toInitialSegment.trans (f.trans h₁.symm.toInitialSegment)⟩

instance : LT Ordinal where
  lt := lift₂ (fun r s => Nonempty (r ≺r s)) <| by
    intro α₀ β₀ α₁ β₁ r₀ r₁ s₀ s₁ _ _ _ _ h₀ h₁
    simp
    apply Iff.intro
    · intro ⟨f⟩
      exact ⟨h₀.symm.toInitialSegment.trans_princ (f.trans_init h₁.toInitialSegment)⟩
    · intro ⟨f⟩
      exact ⟨h₀.toInitialSegment.trans_princ (f.trans_init h₁.symm.toInitialSegment)⟩

def type_in_ty (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) := { x: α // r x a }
def type_in_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) (x y: type_in_ty r a) : Prop := r x.val y.val

def type_in_rel_to_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : type_in_rel r a ↪r r where
  toFun x := x.val
  inj := by intro a b h; cases a; cases b; cases h; rfl
  map_rel := Iff.rfl

instance {α: Type*} (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Relation.IsWellOrder (type_in_rel r a) :=
  (type_in_rel_to_rel r a).liftWellOrder
def type_in (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Ordinal := type (type_in_rel r a)

def type_in_lt_type (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : type_in r a < type r := by
  refine ⟨{
    toFun := Subtype.val
    inj := Subtype.val_inj
    map_rel := Iff.rfl
    isPrincipal := by
      exists a
      intro b
      apply Iff.intro
      · intro h
        simp; exists ⟨_, h⟩
      · rintro ⟨a, _, rfl⟩
        exact a.property
  }⟩

def of_lt_type {r: α -> α -> Prop} [Relation.IsWellOrder r] : ∀{o}, o < type r -> ∃a, o = type_in r a := by
  intro o hi
  induction o with | @type β s =>
  have ⟨f⟩ := hi; simp at f
  have ⟨top, htop⟩ := f.IsPrincipal
  have (a: { a // r a top }) : ∃b, a = f b := by simpa using (htop a.val).mp a.property
  replace this := Classical.axiomOfChoice this
  obtain ⟨g, hg⟩ := this
  exists top
  apply sound
  exact {
    toFun b := {
      val := f b
      property := by
        apply (htop _).mpr
        apply Set.mem_range'
    }
    invFun := g
    map_rel := map_rel f
    leftInv _ := by
      dsimp; congr; symm
      apply hg
    rightInv _ := by
      symm; dsimp
      apply f.inj
      show f _ = f _
      rw [←hg]
  }

def ulift_rel (r: α -> α -> Prop) : ULift α -> ULift α -> Prop := fun a b => r a.down b.down

def ulift_rel_eqv_rel (r: α -> α -> Prop) : ulift_rel r ≃r r where
  toFun x := x.down
  invFun x := ⟨x⟩
  leftInv _ := rfl
  rightInv _ := rfl
  map_rel := Iff.rfl

instance [Relation.IsWellOrder r] : Relation.IsWellOrder (ulift_rel r) := (ulift_rel_eqv_rel r).toRelEmbedding.liftWellOrder

def ulift.{v, u} : Ordinal.{u} -> Ordinal.{max u v} :=
  lift (fun r => type (ulift_rel r)) <| by
    intro α β r s _ _ h
    dsimp
    apply sound
    apply (ulift_rel_eqv_rel _).trans
    apply h.trans
    exact (ulift_rel_eqv_rel _).symm

def omega': Ordinal.{0} := type (α := ℕ) (· < ·)
def omega.{u} := ulift.{u} omega'

def ofNat' (n: ℕ) := type (α := Fin n) (· < ·)
def ofNat.{u} (n: ℕ) := ulift.{u} (ofNat' n)

def lt_omega_iff : ∀{o: Ordinal.{u}}, o < omega ↔ ∃n, o = ofNat n := by
  intro o
  apply Iff.intro
  · induction o with | type r =>
    intro ⟨g⟩
    dsimp at g
    replace g := g.trans_init (ulift_rel_eqv_rel _).toInitialSegment
    have ⟨n, hn⟩ := g.IsPrincipal
    dsimp at hn
    have  hg (x): g x < n := by
      apply (hn _).mpr
      apply Set.mem_range'
    replace hn (x: Fin n) := (hn x).mp x.isLt
    simp at hn; replace hn := Classical.axiomOfChoice hn
    obtain ⟨f, hf⟩ := hn
    exists n
    apply sound
    apply RelEquiv.trans _ (ulift_rel_eqv_rel _).symm
    simp
    exact {
      toFun x := {
          val := g x
          isLt := hg _
      }
      invFun := f
      map_rel := map_rel g
      leftInv x := by simp; congr; symm; apply hf
      rightInv := by
        intro x
        simp; apply g.inj
        show g _ = g _
        rw [←hf]
    }
  · rintro ⟨n, rfl⟩
    refine ⟨?_⟩
    simp
    apply (ulift_rel_eqv_rel _).toInitialSegment.trans_princ
    apply PrincipalSegment.trans_init _ (ulift_rel_eqv_rel _).symm.toInitialSegment
    exact {
      toFun := Fin.val
      inj _ _ := Fin.val_inj.mp
      map_rel := Iff.rfl
      isPrincipal := by
        exists n; intro m
        simp
        apply Iff.intro
        · intro h
          exists ⟨_, h⟩
        · rintro ⟨_, rfl⟩
          apply Fin.isLt
    }

inductive succ_rel (r: α -> α -> Prop) : Option α -> Option α -> Prop where
| some_lt_none : succ_rel r (.some a) .none
| some_lt_some : r a b ->  succ_rel r (.some a) (.some b)

instance [Relation.IsWellOrder r] : Relation.IsWellOrder (succ_rel r) where
  trans {a b c} h g := by
    cases h <;> cases g
    apply succ_rel.some_lt_none
    apply succ_rel.some_lt_some
    apply Relation.trans
    assumption
    assumption
  trichotomous := by
    intro a b
    rcases a with _ | a <;> rcases b with _ | b
    right; left; rfl
    right; right; apply succ_rel.some_lt_none
    left; apply succ_rel.some_lt_none
    rcases Relation.trichotomous r a b with h | h | h
    left; apply succ_rel.some_lt_some; assumption
    right; left; congr
    right; right; apply succ_rel.some_lt_some; assumption
  wf := by
    suffices ih:∀a, Acc (succ_rel r) (.some a) by
      apply WellFounded.intro
      intro a
      cases a
      apply Acc.intro
      intro y h; cases h
      apply ih
      apply ih
    intro a
    induction a using (Relation.wf r).induction with
    | _ a ih =>
    apply Acc.intro
    intro _ h; cases h
    apply ih
    assumption

def succ : Ordinal -> Ordinal :=
  lift (fun r => type (succ_rel r)) <| by
    intro α β r s _ _ h
    simp; apply sound
    exact {
      toEquiv := Equiv.optionCongr h.toEquiv
      map_rel := by
        intro a b
        cases a <;> cases b <;> simp
        all_goals (apply Iff.intro <;> intro g)
        any_goals contradiction
        any_goals apply succ_rel.some_lt_none
        all_goals apply succ_rel.some_lt_some
        apply map_rel_fwd h
        cases g; assumption
        cases g
        apply map_rel_rev h
        assumption
    }

def lt_succ_self (o: Ordinal) : o < o.succ := by
  induction o with | @type α r =>
  exact ⟨{
      toFun := .some
      inj _ _ := Option.some.inj
      map_rel := by
        simp; intro a b
        apply Iff.intro
        apply succ_rel.some_lt_some
        intro h; cases h; assumption
      isPrincipal := by
        exists .none
        simp; intro b
        apply Iff.intro
        intro h; cases h
        exact ⟨_, rfl⟩
        rintro ⟨_, rfl⟩
        apply succ_rel.some_lt_none
  }⟩

instance : IsPartialOrder Ordinal where
  lt_iff_le_and_not_ge := by
    intro a b
    induction a with | @type α r =>
    induction b with | @type β s =>
    apply Iff.intro
    · intro ⟨h⟩
      apply And.intro ⟨h.toInitialSegment⟩
      intro ⟨g⟩
      simp at h g
      exact (h.trans_init g).irrefl
    · intro ⟨⟨h⟩, g⟩
      simp at h
      replace h := h
      rcases h.principal_or_eqv with ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩
      · exact ⟨h⟩
      · nomatch g ⟨h.symm.toInitialSegment⟩
  refl a := by
    induction a with | type r =>
    exact ⟨.id _⟩
  trans {a b c} h g := by
    induction a with | type ra =>
    induction b with | type rb =>
    induction c with | type rc =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    exact ⟨h.trans g⟩
  antisymm {a b} h g := by
    induction a with | type ra =>
    induction b with | type rb =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    apply sound
    exact h.antisymm g

end Ordinal
