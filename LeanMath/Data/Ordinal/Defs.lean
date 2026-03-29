import LeanMath.Tactic.PPWithUniv
import LeanMath.Tactic.AxiomBlame
import LeanMath.Logic.Relation.Segments
import LeanMath.Order.Set
import LeanMath.Order.ConditionallyCompleteLattice
import LeanMath.Logic.Small.Defs
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

@[cases_eliminator]
def ind {motive: Ordinal -> Prop} (type: ∀{α} (r: α -> α -> Prop) [Relation.IsWellOrder r], motive (type r)) : ∀o, motive o := by
  intro ⟨o⟩
  induction o using Quotient.ind with | _ o =>
  apply type

def exists_eq_type: ∀o: Ordinal, ∃(α: _) (r: α -> α -> Prop) (_: Relation.IsWellOrder r), o = type r  := by
  intro o
  cases o with | _ =>
  refine ⟨_, _, _, rfl⟩

def sound {r: α -> α -> Prop} {s: β -> β -> Prop} [Relation.IsWellOrder r] [Relation.IsWellOrder s] : r ≃r s -> type r = type s := by
  intro h
  unfold type; congr 1
  apply Quotient.sound
  exact ⟨h⟩

noncomputable def exact {r: α -> α -> Prop} {s: β -> β -> Prop} [Relation.IsWellOrder r] [Relation.IsWellOrder s] : type r = type s -> r ≃r s := by
  intro h
  replace h := (Quotient.exact (Ordinal.ofQuot.inj h))
  exact Classical.choice <| by cases h; refine ⟨?_⟩; assumption

instance : LE Ordinal where
  le := lift₂ (fun r s => Nonempty (r ≼r s)) <| by
    intro α₀ β₀ α₁ β₁ r₀ r₁ s₀ s₁ _ _ _ _ h₀ h₁
    simp
    apply Iff.intro
    · intro ⟨f⟩
      exact ⟨h₀.symm.toInitialSegment.trans (f.trans h₁.toInitialSegment)⟩
    · intro ⟨f⟩
      exact ⟨h₀.toInitialSegment.trans (f.trans h₁.symm.toInitialSegment)⟩

instance [LEM] : LT Ordinal where
  lt := lift₂ (fun r s => Nonempty (r ≺r s)) <| by
    intro α₀ β₀ α₁ β₁ r₀ r₁ s₀ s₁ _ _ _ _ h₀ h₁
    simp
    apply Iff.intro
    · intro ⟨f⟩
      exact ⟨h₀.symm.toInitialSegment.trans_princ (f.trans_init h₁.toInitialSegment)⟩
    · intro ⟨f⟩
      exact ⟨h₀.toInitialSegment.trans_princ (f.trans_init h₁.symm.toInitialSegment)⟩

private def rank_ty (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) := { x: α // r x a }
private def rank_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) (x y: rank_ty r a) : Prop := r x.val y.val

private def rank_rel_to_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : rank_rel r a ↪r r where
  toFun x := x.val
  inj := by intro a b h; cases a; cases b; cases h; rfl
  map_rel := Iff.rfl

private instance {α: Type*} (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Relation.IsWellOrder (rank_rel r a) :=
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

def rank_lt_type [LEM] (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : rank r a < type r := ⟨rank_lt_type' r a⟩

def rank_lt_rank_iff [LEM] {r: α -> α -> Prop} [Relation.IsWellOrder r] {a b: α} : r a b ↔ rank r a < rank r b := by
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
      simp; show ∃i, (h i).val = x
      have := h ⟨_, rxa⟩
      exists ⟨x, rxa⟩
      show (h.trans_init (rank_lt_type' r b).toInitialSegment) ⟨x, rxa⟩ = rank_lt_type' r a ⟨x, rxa⟩
      congr
      apply Subsingleton.allEq
    · rintro ⟨x, _, rfl⟩
      suffices (h.trans_init (rank_lt_type' r b).toInitialSegment) = rank_lt_type' r a by
        rw [this]; exact x.property
      apply Subsingleton.allEq

def rank_inj [LEM] {r: α -> α -> Prop} [Relation.IsWellOrder r] {a b: α} : rank r a = rank r b -> a = b := by
  intro eq
  rcases Relation.trichotomous r a b with h | h | h
  · rw [rank_lt_rank_iff (r := r), eq, ←rank_lt_rank_iff] at h
    nomatch Relation.irrefl h
  · assumption
  · rw [rank_lt_rank_iff (r := r), eq, ←rank_lt_rank_iff] at h
    nomatch Relation.irrefl h

def of_lt_type [LEM] {r: α -> α -> Prop} [Relation.IsWellOrder r] : ∀{o}, o < type r -> ∃a, o = rank r a := by
  intro o hi
  cases o with | @type β s =>
  have ⟨f⟩ := hi; simp at f
  have ⟨top, htop⟩ := f.IsPrincipal
  have (a: { a // r a top }) : existsUnique fun b => f b = a := by
    obtain ⟨a, ha⟩ := (htop a.val).mp a.property
    refine ⟨a, ha, ?_⟩
    intro b hb
    apply inj f
    rw [ha, ←hb]
  replace this := Classical.axiomOfUniqueChoice this
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
      apply (hg _).left.symm
    rightInv _ := by
      symm; dsimp
      apply f.inj
      show f _ = f _
      rw [(hg _).left]
  }

private def ulift_rel (r: α -> α -> Prop) : ULift α -> ULift α -> Prop := fun a b => r a.down b.down

private def ulift_rel_eqv_rel (r: α -> α -> Prop) : ulift_rel r ≃r r where
  toFun x := x.down
  invFun x := ⟨x⟩
  leftInv _ := rfl
  rightInv _ := rfl
  map_rel := Iff.rfl

private instance [Relation.IsWellOrder r] : Relation.IsWellOrder (ulift_rel r) := (ulift_rel_eqv_rel r).toRelEmbedding.liftWellOrder

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

instance : NatCast Ordinal where
  natCast := ofNat

instance : OfNat Ordinal n where
  ofNat := n

def lt_omega_iff [LEM] : ∀{o: Ordinal.{u}}, o < omega ↔ ∃n: ℕ, o = n := by
  intro o
  apply Iff.intro
  · cases o with | type r =>
    intro ⟨g⟩
    dsimp at g
    replace g := g.trans_init (ulift_rel_eqv_rel _).toInitialSegment
    have ⟨n, hn, nunique⟩ := g.IsUniquePrincipal
    have  hg (x): g x < n := by
      apply (hn _).mpr
      apply Set.mem_range'
    replace hn (x: Fin n) := (hn x).mp x.isLt
    let f := (Equiv.ofBij (Bijection.embed_eqv_range g))
    have hf (x): g x = f x := by unfold f; rw [Equiv.apply_ofBij]; rfl
    exists n
    apply sound
    apply RelEquiv.trans _ (ulift_rel_eqv_rel _).symm
    simp
    exact {
      toFun x := {
          val := g x
          isLt := hg _
      }
      invFun x := f.symm ⟨x, hn _⟩
      map_rel := map_rel g
      leftInv x := by
        dsimp; congr
        rw [hf, Equiv.symm_coe]
      rightInv := by
        intro x
        simp; apply g.inj
        show g _ = g _
        rw [hf, Equiv.symm_coe]
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

private inductive succ_rel (r: α -> α -> Prop) : Option α -> Option α -> Prop where
| some_lt_none : succ_rel r (.some a) .none
| some_lt_some : r a b ->  succ_rel r (.some a) (.some b)

private instance [Relation.IsWellOrder r] : Relation.IsWellOrder (succ_rel r) where
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
      toEquiv := Equiv.option_congr h.toEquiv
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

def lt_succ_self [LEM] (o: Ordinal) : o < o.succ := by
  cases o with | @type α r =>
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

instance [LEM] : IsPartialOrder Ordinal where
  lt_iff_le_and_not_ge := by
    intro a b
    cases a with | @type α r =>
    cases b with | @type β s =>
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
    cases a with | type r =>
    exact ⟨.id _⟩
  trans {a b c} h g := by
    cases a with | type ra =>
    cases b with | type rb =>
    cases c with | type rc =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    exact ⟨h.trans g⟩
  antisymm {a b} h g := by
    cases a with | type ra =>
    cases b with | type rb =>
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
      toEquiv := Equiv.sum_congr h₀.toEquiv h₁.toEquiv
      map_rel {a b} := by
        simp
        rcases a with a | a <;> rcases b with b | b <;> simp
        apply map_rel h₀
        apply map_rel h₁
    }

private def lt_trichotomy_of_le [LEM] (o: Ordinal) : ∀{a b: Ordinal}, a ≤ o -> b ≤ o -> a < b ∨ a = b ∨ b < a := by
  intro a b ha hb
  replace ha := lt_or_eq_of_le ha
  replace hb := lt_or_eq_of_le hb
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · cases o with | type r =>
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
  cases a with | @type α r =>
  cases b with | @type β s =>
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

def le_add_right [LEM] (a b: Ordinal.{u}) : b ≤ a + b := by
  cases a with | @type α r =>
  cases b with | @type β s =>
  refine ⟨?_⟩
  apply InitialSegment.collapse
  dsimp
  exact {
    toFun := .inr
    inj _ _ := Sum.inr.inj
    map_rel := by simp
  }

instance [LEM] : @Relation.IsTrichotomous Ordinal (· < ·) (· = ·) where
  trichotomous := by
    intro a b
    apply lt_trichotomy_of_le (a + b)
    apply le_add_left
    apply le_add_right

instance [LEM] : IsLinearOrder Ordinal where

instance [LEM] : @Relation.IsWelFounded Ordinal (· < ·) where
  wf := by
    apply WellFounded.intro
    intro o
    cases o with | @type α r =>
    apply Acc.intro
    intro x hx
    obtain ⟨a, rfl⟩ := of_lt_type hx
    clear hx
    induction a using (Relation.wf r).induction with
    | h a ih =>
    apply Acc.intro
    intro b h
    obtain ⟨b, rfl⟩ := of_lt_type <| Relation.trans h (rank_lt_type r _)
    apply ih
    rwa [←rank_lt_rank_iff] at h

instance [LEM] : WellFoundedRelation Ordinal where
  rel a b := a < b
  wf := Relation.wf _

private structure min_rel_ty {α β: Type u} (r: α -> α -> Prop) (s: β -> β -> Prop) [Relation.IsWellOrder r] [Relation.IsWellOrder s] where
  left: α
  right: β
  rank_eq: rank r left = rank s right

private def min_rel {α β: Type u} (r: α -> α -> Prop) (s: β -> β -> Prop) [Relation.IsWellOrder r] [Relation.IsWellOrder s] (x y: min_rel_ty r s) : Prop := r x.left y.left

variable {r: α -> α -> Prop} {s: β -> β -> Prop} {t: γ -> γ -> Prop}
   {r₀: α₀ -> α₀ -> Prop} {r₁: α₁ -> α₁ -> Prop}
   {s₀: β₀ -> β₀ -> Prop} {s₁: β₁ -> β₁ -> Prop}
   [Relation.IsWellOrder r] [Relation.IsWellOrder s] [Relation.IsWellOrder t]
   [Relation.IsWellOrder r₀] [Relation.IsWellOrder r₁]
   [Relation.IsWellOrder s₀] [Relation.IsWellOrder s₁]

private def min_rel_emb_left [LEM] : min_rel r s ≼r r where
  toFun := min_rel_ty.left
  inj := by
    intro ⟨a, b₀, h₀⟩ ⟨a₁, b₀, h₁⟩ h
    dsimp at h; subst a₁
    congr
    rw [h₀] at h₁
    exact rank_inj h₁
  map_rel := Iff.rfl
  isInitial := by
    intro x a h
    have this : rank r a < rank r x.left := by rwa [←rank_lt_rank_iff]
    rw [x.rank_eq] at this
    have ⟨b, rank_eq⟩ := of_lt_type (lt_trans this (rank_lt_type _ _))
    exists ⟨a, b, rank_eq⟩

private def min_rel_emb_right [LEM] : min_rel r s ≼r s where
  toFun := min_rel_ty.right
  inj := by
    intro ⟨a, b₀, h₀⟩ ⟨a₁, b₀, h₁⟩ h
    dsimp at h; subst b₀
    congr
    rw [←h₀] at h₁
    exact rank_inj h₁.symm
  map_rel := by
    intro x y
    rw [rank_lt_rank_iff (r := s), ←x.rank_eq, ←y.rank_eq]
    rw [←rank_lt_rank_iff]
    apply map_rel min_rel_emb_left
  isInitial := by
    intro x b h
    have this : rank s b < rank s x.right := by rwa [←rank_lt_rank_iff]
    rw [←x.rank_eq] at this
    have ⟨a, rank_eq⟩ := of_lt_type (lt_trans this (rank_lt_type _ _))
    exists ⟨a, b, rank_eq.symm⟩

private instance [LEM] : Relation.IsWellOrder (min_rel r s) := min_rel_emb_left.liftWellOrder

def rank_eq_of_init {F: Type*} [EmbeddingLike F α β] [IsInitialSegment F r s] (f: F)
  : rank r a = rank s (f a) := by
  have ⟨g, hg⟩ := Classical.axiomOfChoice fun x: { b // s b (f a) } => Set.mem_range.mp (isInitial f a x.val x.property)
  apply sound
  exact {
    toFun x := {
      val := f x.val
      property := by
        apply map_rel_fwd
        exact x.property
    }
    invFun x := {
      val := g x
      property := by
        apply map_rel_rev f
        rw [hg]
        exact x.property
    }
    map_rel := map_rel f
    leftInv := by intro ⟨x, hx⟩; dsimp; congr; rw [hg]
    rightInv := by
      intro ⟨x, hx⟩
      dsimp
      congr; apply inj f
      rw [hg]
  }

instance [LEM] : Min Ordinal.{u} where
  min := lift₂ (fun r s => type (min_rel r s)) <| by
    intro α₀ β₀ α₁ β₁ r₀ r₁ s₀ s₁ _ _ _ _ h g
    dsimp; apply sound
    exact {
      toFun x := {
        left := h x.left
        right := g x.right
        rank_eq := by
          rw [←rank_eq_of_init, ←rank_eq_of_init]
          exact x.rank_eq
      }
      invFun x := {
        left := h.symm x.left
        right := g.symm x.right
        rank_eq := by
          rw [←rank_eq_of_init, ←rank_eq_of_init]
          exact x.rank_eq
      }
      rightInv  := by intro ⟨x, y, h⟩; simp
      leftInv := by intro ⟨x, y, h⟩; simp
      map_rel := by
        intro x y
        apply map_rel h
    }

instance [LEM] : IsSemiLatticeMin Ordinal where
  min_le_left {a b} := by
    cases a with | _ r =>
    cases b with | _ s =>
    exact ⟨min_rel_emb_left⟩
  min_le_right {a b} := by
    cases a with | _ r =>
    cases b with | _ s =>
    exact ⟨min_rel_emb_right⟩
  le_min x {a b} f g := by
    cases x with | @type γ t =>
    cases a with | @type α r =>
    cases b with | @type β s =>
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    refine ⟨?_⟩
    dsimp
    exact {
      toFun x := {
        left := f x
        right := g x
        rank_eq := by rw [←rank_eq_of_init, ←rank_eq_of_init]
      }
      inj := by
        intro x y h
        dsimp at h
        exact inj f (min_rel_ty.mk.inj h).left
      map_rel := map_rel f
      isInitial := by
        intro x b h
        simp
        replace h : r b.left (f x) := h
        have ⟨y, hy⟩ := Set.mem_range.mp (isInitial f _ _ h)
        dsimp at y
        exists y
        obtain ⟨b₀, b₁, hb⟩ := b
        dsimp at h hy
        rw [←hy] at h
        replace h : t y x := map_rel_rev f h
        show min_rel_ty.mk _ _ _ = _
        congr; apply rank_inj (r := s)
        rw [←hb, ←rank_eq_of_init, rank_eq_of_init f]
        dsimp
        rw [hy]
    }

section

variable  (r: α -> α -> Prop) (s: β -> β -> Prop) [Relation.IsWellOrder r] [Relation.IsWellOrder s]

private def sum_rank : α ⊕ β -> Ordinal
| .inl a => rank r a
| .inr b => rank s b

private def max_rel_setoid : Setoid (α ⊕ β) where
  r a b := sum_rank r s a = sum_rank r s b
  iseqv := Relation.equiv _

private def max_rel_ty := Quotient (max_rel_setoid r s)

private def max_rel_ty.rank : max_rel_ty r s -> Ordinal :=
  Quotient.lift (fun
    | .inl x => Ordinal.rank r x
    | .inr x => Ordinal.rank s x) fun _ _ => id

private def max_rel [LEM] (a b: max_rel_ty r s) := a.rank < b.rank

private def max_rel_init_ord [LEM] : max_rel r s ↪r ((· < ·): Ordinal -> Ordinal -> Prop) where
  toFun a := a.rank
  inj := by
    intro a b h
    dsimp at h
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    apply Quotient.sound
    assumption
  map_rel := Iff.rfl

instance [LEM] : Relation.IsWellOrder (max_rel r s) := (max_rel_init_ord r s).liftWellOrder

end

@[simp]
private def quot_lift_mk {s: Setoid α} {x: α} {f: α -> β} {h} :
  Quotient.lift f h (Quotient.mk s x) = f x := rfl

private def max_rel_congr_init [LEM] (f: r₀ ≼r r₁) (g: s₀ ≼r s₁) : max_rel r₀ s₀ ≼r max_rel r₁ s₁ where
  toFun := Quotient.lift (fun x => Quotient.mk _ (x.map f g)) <| by
    intro a b h
    dsimp
    apply Quotient.sound
    cases a <;> cases b <;> (dsimp; show Ordinal.rank _ _ = Ordinal.rank _ _)
    all_goals
      iterate 2 rw [←rank_eq_of_init]
      assumption
  inj := by
    intro a b h
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    replace h := Quotient.exact h
    apply Quotient.sound
    show sum_rank _ _ _ = sum_rank _ _ _
    cases a <;> cases b <;> (dsimp [sum_rank]; dsimp at h)
    all_goals
      replace h : Ordinal.rank _ _ = Ordinal.rank _ _ := h
      rwa [←rank_eq_of_init, ←rank_eq_of_init] at h
  map_rel := by
    intro a b
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    cases a <;> cases b
    all_goals simp [max_rel, max_rel_ty.rank, ←rank_eq_of_init f, ←rank_eq_of_init g]
  isInitial := by
    intro a b
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    cases a <;> cases b
    all_goals
      simp [max_rel, max_rel_ty.rank]
      intro h
      replace h : _ < Ordinal.rank _ _ := h
      rename_i x₀ x₁
    any_goals rw [←rank_lt_rank_iff] at h
    · obtain ⟨x₁, rfl⟩ := Set.mem_range.mp <| f.IsInitial x₀ x₁ h
      exists Quotient.mk _ (Sum.inl x₁)
    · rw [←rank_eq_of_init] at h
      obtain ⟨x₁, g⟩ := of_lt_type (lt_trans h (rank_lt_type _ _))
      exists Quotient.mk _ (Sum.inl x₁)
      apply Quotient.sound
      simp; show Ordinal.rank _ _ = Ordinal.rank _ _
      symm; rwa [←rank_eq_of_init]
    · rw [←rank_eq_of_init] at h
      obtain ⟨x₁, g⟩ := of_lt_type (lt_trans h (rank_lt_type _ _))
      exists Quotient.mk _ (Sum.inr x₁)
      apply Quotient.sound
      simp; show Ordinal.rank _ _ = Ordinal.rank _ _
      symm; rwa [←rank_eq_of_init]
    · obtain ⟨x₁, rfl⟩ := Set.mem_range.mp <| g.IsInitial x₀ x₁ h
      exists Quotient.mk _ (Sum.inr x₁)

private def emb_max_rel_left [LEM] : r ≼r max_rel r s where
  toFun x := Quotient.mk _ (.inl x)
  inj _ _ h := rank_inj (Quotient.exact h)
  map_rel := rank_lt_rank_iff
  isInitial := by
    intro a b h
    replace h : max_rel r s b (Quotient.mk _ (.inl a)) := h
    induction b using Quotient.ind with | _ b =>
    rcases b with b | b <;> replace h : Ordinal.rank _ b < Ordinal.rank _ a := h
    exists b
    have ⟨b', h⟩ := of_lt_type (lt_trans h (rank_lt_type _ _))
    simp; exists b'
    apply Quotient.sound
    apply Relation.symm
    assumption

private def emb_max_rel_right [LEM] : s ≼r max_rel r s where
  toFun x := Quotient.mk _ (.inr x)
  inj _ _ h := rank_inj (Quotient.exact h)
  map_rel := rank_lt_rank_iff
  isInitial := by
    intro a b h
    replace h : max_rel r s b (Quotient.mk _ (.inr a)) := h
    induction b using Quotient.ind with | _ b =>
    rcases b with b | b <;> replace h : Ordinal.rank _ b < Ordinal.rank _ a := h
    have ⟨b', h⟩ := of_lt_type (lt_trans h (rank_lt_type _ _))
    simp; exists b'
    apply Quotient.sound
    apply Relation.symm
    assumption
    exists b

instance [LEM] : Max Ordinal where
  max := lift₂ (fun r s => type (max_rel r s)) <| by
    intro α₀ β₀ α₁ β₁ r₀ r₁ s₀ s₁ _ _ _ _ f g
    apply sound
    apply InitialSegment.antisymm
    apply max_rel_congr_init
    exact f.toInitialSegment
    exact g.toInitialSegment
    apply max_rel_congr_init
    exact f.symm.toInitialSegment
    exact g.symm.toInitialSegment

instance [LEM] : IsLattice Ordinal where
  left_le_max {a b} := by
    cases a with | type r =>
    cases b with | type s =>
    exact ⟨emb_max_rel_left⟩
  right_le_max {a b} := by
    cases a with | type r =>
    cases b with | type s =>
    exact ⟨emb_max_rel_right⟩
  max_le := by
    intro x a b f g
    cases x with | @type γ t =>
    cases a with | @type α r =>
    cases b with | @type β s =>
    obtain ⟨f⟩ := f
    obtain ⟨g⟩ := g
    dsimp at f g
    refine ⟨?_⟩
    dsimp
    exact {
      toFun := Quotient.lift (fun x => x.elim f g) <| by
        intro a b h
        dsimp
        cases a <;> cases b
        all_goals
          rename_i a b
          replace h : Ordinal.rank _ _ = Ordinal.rank _ _ := h
          simp
        congr; exact rank_inj h
        apply rank_inj (r := t)
        rwa [←rank_eq_of_init, ←rank_eq_of_init]
        apply rank_inj (r := t)
        rwa [←rank_eq_of_init, ←rank_eq_of_init]
        congr; exact rank_inj h
      inj := by
        intro a b h
        induction a using Quotient.ind with | _ a =>
        induction b using Quotient.ind with | _ b =>
        cases a <;> cases b
        all_goals simp at h
        congr; exact inj f h
        apply Quotient.sound
        show Ordinal.rank _ _ = Ordinal.rank _ _
        rw [rank_eq_of_init f, rank_eq_of_init g, h]
        apply Quotient.sound
        show Ordinal.rank _ _ = Ordinal.rank _ _
        rw [rank_eq_of_init f, rank_eq_of_init g, h]
        congr; exact inj g h
      map_rel := by
        intro a b
        induction a using Quotient.ind with | _ a =>
        induction b using Quotient.ind with | _ b =>
        cases a <;> cases b
        all_goals simp [max_rel, max_rel_ty.rank]
        all_goals repeat rw [rank_eq_of_init f]
        all_goals repeat rw [rank_eq_of_init g]
        all_goals apply rank_lt_rank_iff.symm
      isInitial := by
        intro a b h
        induction a using Quotient.ind with | _ a =>
        rcases a with a | a
        obtain ⟨b, rfl⟩ := Set.mem_range.mp <| f.isInitial a b h
        simp; exists Quotient.mk _ (.inl b)
        obtain ⟨b, rfl⟩ := Set.mem_range.mp <| g.isInitial a b h
        simp; exists Quotient.mk _ (.inr b)
    }

noncomputable instance [LEM] : InfSet Ordinal where
  sInf S :=
    open UniqueChoice in
    if h:S.Nonempty then
      Set.min (· < ·) h
    else
      0

def sInf_mem [LEM] (U: Set Ordinal) (hU: U.Nonempty) : ⨅ U ∈ U := by
  simp [sInf]
  rw [dif_pos hU]
  apply Set.min_mem

private protected def sInf_le [LEM] (U: Set Ordinal) : ∀u ∈ U, ⨅ U ≤ u := by
  intro u hu
  simp [sInf]
  rw [dif_pos ⟨_, hu⟩]
  apply le_of_not_lt
  intro h
  exact Set.min_minimal (· < ·) (U := U) ⟨_, hu⟩ u hu h

private protected def le_sInf [LEM] (U: Set Ordinal) (hU: U.Nonempty) (x: Ordinal) (h: ∀u ∈ U, x ≤ u) : x ≤ ⨅ U := by
  classical
  apply le_of_not_lt
  intro g
  have (u: Ordinal) (hu: u ∈ U) : sInf U < u := by
    apply lt_of_lt_of_le g
    apply h
    assumption
  exact Relation.irrefl (this _ (sInf_mem  U hU))

def ulift_le_ulift {a b: Ordinal.{u}} : ulift.{v} a ≤ ulift b ↔ a ≤ b := by
  cases a with | @type α r =>
  cases b with | @type β s =>
  apply Iff.intro
  · intro h
    obtain ⟨h⟩ := h; refine ⟨?_⟩
    dsimp; dsimp at h
    apply InitialSegment.trans
    apply RelEquiv.toInitialSegment
    apply RelEquiv.symm
    apply ulift_rel_eqv_rel
    apply flip InitialSegment.trans
    apply RelEquiv.toInitialSegment
    apply ulift_rel_eqv_rel
    assumption
  · intro h
    obtain ⟨h⟩ := h; refine ⟨?_⟩
    dsimp; dsimp at h
    apply InitialSegment.trans
    apply RelEquiv.toInitialSegment
    apply ulift_rel_eqv_rel
    apply flip InitialSegment.trans
    apply RelEquiv.toInitialSegment
    apply RelEquiv.symm
    apply ulift_rel_eqv_rel
    assumption

noncomputable instance [LEM] : SupSet Ordinal where
  sSup S := sInf S.upperBounds

protected def sSup_eq_sInf_upperBounds [LEM] (U: Set Ordinal) : ⨆ U = ⨅ U.upperBounds := rfl

instance [LEM] : IsConditionallyCompleteLattice Ordinal where
  csInf_le _ := Ordinal.sInf_le _ _
  le_csInf h g := Ordinal.le_sInf _ h _ g
  le_csSup := by
    intro S a ha hs; rw [Ordinal.sSup_eq_sInf_upperBounds]
    apply le_sInf
    assumption
    intro u hu
    apply hu
    assumption
  csSup_le := by
    intro U a hU ha
    rw [Ordinal.sSup_eq_sInf_upperBounds]
    apply sInf_le
    assumption

instance [LEM] : IsLawfulInf Ordinal where
  sInf_le := Ordinal.sInf_le

private noncomputable def out (o: Ordinal.{u}) : Pre.{u} :=
  Classical.choose o.toQuot.exists_rep

def ToType (o: Ordinal.{u}) : Type u := o.out.ty
def ToType_rel (o: Ordinal.{u}) : o.ToType -> o.ToType -> Prop := o.out.rel

instance (o: Ordinal) : Relation.IsWellOrder o.ToType_rel := o.out.wo

instance (o: Ordinal) : LT o.ToType where
  lt := o.ToType_rel
instance (o: Ordinal) : LE o.ToType where
  le a b := ¬b < a

instance (o: Ordinal) : @Relation.IsWellOrder o.ToType (· < ·) := o.out.wo

instance (o: Ordinal) : IsLinearOrder o.ToType where
  lt_iff_le_and_not_ge {a b} := by
    apply Iff.intro
    · intro h
      apply And.intro
      intro g
      exact Relation.asymm h g
      intro g; exact g h
    · intro ⟨g₀, g₁⟩
      rcases lt_trichotomy a b with h' | h' | h'
      assumption
      subst b
      contradiction
      contradiction
  refl _ := Relation.irrefl (R := (· < ·))
  trans := by
    intro a b c h g x
    rcases lt_trichotomy a b with h' | h' | h'
    have := Relation.trans x h'
    contradiction
    subst a; contradiction
    contradiction
  antisymm {a b} h g := by
    rcases lt_trichotomy a b with h' | h' | h'
    contradiction
    assumption
    contradiction

@[simp] def type_toType (o: Ordinal) : type (· < ·: o.ToType -> o.ToType -> Prop) = o := by
   have := (Classical.choose_spec o.toQuot.exists_rep)
   show Ordinal.ofQuot _ = Ordinal.ofQuot _
   congr

def enum_bij [LEM] (r : α → α → Prop) [Relation.IsWellOrder r] : α ↭ Set.Iio (type r) where
  toFun x := {
    val := rank r x
    property := by apply rank_lt_type
  }
  inj' := by
    intro a b h
    exact rank_inj (Subtype.mk.inj h)
  surj' := by
    intro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := of_lt_type hx
    exists a

noncomputable def enum [LEM] (r : α → α → Prop) [Relation.IsWellOrder r] : (· < · : Set.Iio (type r) → Set.Iio (type r) → Prop) ≃r r := RelEquiv.symm {
  toEquiv := Equiv.ofBij (enum_bij r)
  map_rel {a b} := by
    dsimp
    rw [Equiv.apply_ofBij, Equiv.apply_ofBij]
    show r a b ↔ rank r a < rank r b
    rw [←rank_lt_rank_iff]
}

def enum_symm_eq_rank [LEM] (r : α → α → Prop) [Relation.IsWellOrder r] : (enum r).symm x = rank r x := by
  unfold enum
  show ((Equiv.ofBij (enum_bij r)).symm.symm x).val = _
  rw [Equiv.symm_symm, Equiv.apply_ofBij]
  rfl

noncomputable def ToType.mk [LEM] {o: Ordinal} : Set.Iio o ≃o o.ToType where
  toFun x := enum (· < ·) {
    val := x.val
    property := type_toType _ ▸ x.property
  }
  invFun x := {
    val := (enum (· < ·)).symm x
    property := by
      show _ < o
      rw [enum_symm_eq_rank]
      conv => { rhs; rw [←type_toType o] }
      apply rank_lt_type
  }
  leftInv := by
    intro x
    dsimp
    show (enum _ ((enum _).symm x)) = x
    rw [RelEquiv.symm_coe]
  rightInv := by
    intro x
    dsimp
    ext; dsimp
    show ((enum _).symm (enum _ _)) = x.val
    rw [RelEquiv.coe_symm]
  map_rel {a b} := by
    rw [←not_lt (α := o.ToType)]
    rw [←map_rel (enum (· < ·: o.ToType -> o.ToType -> Prop))]
    show a.val ≤ b.val ↔ _
    rw [←not_lt]
    rfl

instance small_Iio [LEM] (o : Ordinal.{u}) : Small.{u} (Set.Iio o) :=
  ⟨_, ToType.mk.toEquiv⟩

end Ordinal
