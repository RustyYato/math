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

def rank_ty (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) := { x: α // r x a }
def rank_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) (x y: rank_ty r a) : Prop := r x.val y.val

def rank_rel_to_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : rank_rel r a ↪r r where
  toFun x := x.val
  inj := by intro a b h; cases a; cases b; cases h; rfl
  map_rel := Iff.rfl

instance {α: Type*} (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Relation.IsWellOrder (rank_rel r a) :=
  (rank_rel_to_rel r a).liftWellOrder
def rank (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Ordinal := type (rank_rel r a)

def rank_lt_type' (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : rank_rel r a ≺r r where
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

@[simp] def apply_rank_lt_type' (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) {x} : rank_lt_type' r a x = x.val := rfl

def rank_lt_type (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : rank r a < type r := ⟨rank_lt_type' r a⟩

def rank_lt_rank_iff {r: α -> α -> Prop} [Relation.IsWellOrder r] {a b: α} : r a b ↔ rank r a < rank r b := by
  apply Iff.intro
  · intro h
    refine ⟨{
      toFun x := {
        val := x.val
        property := Relation.trans x.property h
      }
      inj := by
        intro ⟨x, hx⟩ ⟨y, hy⟩ h
        dsimp at h
        cases h; rfl
      map_rel := Iff.rfl
      isPrincipal := by
        exists ⟨a, h⟩
        intro ⟨x, hx⟩
        simp; apply Iff.intro
        · intro hbx
          refine ⟨⟨x, ?_⟩, ?_⟩
          exact hbx
          rfl
        · rintro ⟨⟨_, _⟩, h⟩
          cases h
          assumption
    }⟩
  · intro ⟨h⟩
    dsimp at h
    have ⟨top, htop⟩ := h.IsPrincipal
    suffices top.val = a by
      rw [←this]
      exact top.property
    obtain ⟨top, r_top_b⟩ := top
    dsimp
    have htop' : Relation.IsPrincipal r (h.trans_init (rank_lt_type' r b).toInitialSegment) top := Relation.IsPrincipal.trans_init h (PrincipalSegment.toInitialSegment (rank_lt_type' r b)) htop
    suffices ha : Relation.IsPrincipal r (h.trans_init (rank_lt_type' r b).toInitialSegment) a by
      exact Relation.IsPrincipal.unique _ _ htop' ha
    intro x
    apply Iff.intro
    · intro rxa
      simp; show ∃i, x = (h i).val
      have := h ⟨_, rxa⟩
      exists ⟨x, rxa⟩
      show rank_lt_type' r a ⟨x, rxa⟩ = (h.trans_init (rank_lt_type' r b).toInitialSegment) ⟨x, rxa⟩
      congr
      apply Subsingleton.allEq
    · rintro ⟨x, _, rfl⟩
      suffices (h.trans_init (rank_lt_type' r b).toInitialSegment) = rank_lt_type' r a by
        rw [this]; exact x.property
      apply Subsingleton.allEq

def of_lt_type {r: α -> α -> Prop} [Relation.IsWellOrder r] : ∀{o}, o < type r -> ∃a, o = rank r a := by
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
        simp; exact ⟨_, rfl⟩
        rintro ⟨_, _, rfl⟩
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

instance [Relation.IsWellOrder r] [Relation.IsWellOrder s] : Relation.IsWellOrder (Sum.Lex r s) where
  trans {a b c} h g := by
    rcases h with h | h |_ <;> rcases g with g | g | _
    · apply Sum.Lex.inl
      apply Relation.trans
      assumption
      assumption
    · apply Sum.Lex.sep
    · apply Sum.Lex.inr
      apply Relation.trans
      assumption
      assumption
    · apply Sum.Lex.sep
  trichotomous {a b} := by
    rcases a with a | a <;> rcases b with b | b
    · rcases Relation.trichotomous r a b with h | h | h
      · left; apply Sum.Lex.inl
        assumption
      · right; left; congr
      · right; right; apply Sum.Lex.inl
        assumption
    · left; apply Sum.Lex.sep
    · right; right; apply Sum.Lex.sep
    · rcases Relation.trichotomous s a b with h | h | h
      · left; apply Sum.Lex.inr
        assumption
      · right; left; congr
      · right; right; apply Sum.Lex.inr
        assumption
  wf := by
    suffices iha: ∀a, Acc (Sum.Lex r s) (.inl a) by
      apply WellFounded.intro; intro x
      cases x with
      | inl a => apply iha
      | inr a =>
        induction a using (Relation.wf s).induction with
        | _ a ih =>
          apply Acc.intro
          intro _ h; cases h
          apply ih
          assumption
          apply iha
    intro a
    induction a using (Relation.wf r).induction with
    | _ a ih =>
      apply Acc.intro
      intro _ h; cases h
      apply ih
      assumption

instance : Add Ordinal.{u} where
  add := lift₂ (fun r s => type (Sum.Lex r s)) <| by
    intro α₀ β₀ α₁ β₁ r₀ r₁ s₀ s₁ _ _ _ _ h₀ h₁
    simp
    apply sound
    exact {
      toEquiv := Equiv.sumCongr h₀.toEquiv h₁.toEquiv
      map_rel {a b} := by
        simp
        rcases a with a | a <;> rcases b with b | b <;> simp
        apply map_rel h₀
        apply map_rel h₁
    }

private def lt_trichotomy_of_le (o: Ordinal) : ∀{a b: Ordinal}, a ≤ o -> b ≤ o -> a < b ∨ a = b ∨ b < a := by
  classical
  intro a b ha hb
  replace ha := lt_or_eq_of_le ha
  replace hb := lt_or_eq_of_le hb
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · induction o with | type r =>
    obtain ⟨a, rfl⟩ := of_lt_type ha
    obtain ⟨b, rfl⟩ := of_lt_type hb
    simp [←rank_lt_rank_iff]
    rcases Relation.trichotomous r a b with h | h | h
    · left; assumption
    · right; left; congr
    · right; right; assumption
  · left; assumption
  · right; right; assumption
  · right; left; rfl

def le_add_left (a b: Ordinal.{u}) : a ≤ a + b := by
  induction a with | @type α r =>
  induction b with | @type β s =>
  refine ⟨{
    toFun := .inl
    inj _ _ := Sum.inl.inj
    map_rel := by simp
    isInitial := by
      simp
      intro a b h
      cases h
      apply Set.mem_range'
  }⟩

def le_add_right (a b: Ordinal.{u}) : b ≤ a + b := by
  induction a with | @type α r =>
  induction b with | @type β s =>
  refine ⟨?_⟩
  apply PrincipalSegment.collapse
  dsimp
  exact {
    toFun := .inr
    inj _ _ := Sum.inr.inj
    map_rel := by simp
  }

instance : @Relation.IsTrichotomous Ordinal (· < ·) (· = ·) where
  trichotomous := by
    intro a b
    apply lt_trichotomy_of_le (a + b)
    apply le_add_left
    apply le_add_right

instance : IsLinearOrder Ordinal where

end Ordinal
