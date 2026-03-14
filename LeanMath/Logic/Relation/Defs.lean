import LeanMath.Data.Hom
import LeanMath.Data.Embedding.Defs
import LeanMath.Data.Equiv.Defs

class IsRelMap (F: Type*) [FunLike F α β] (r: outParam <| α -> α -> Prop) (s: outParam <| β -> β -> Prop) where
  protected map_rel₀ (f: F) : ∀{a b: α}, r a b -> s (f a) (f b) := by intro f; exact f.map_rel₀

class IsRelHom (F: Type*) [FunLike F α β] (r: outParam <| α -> α -> Prop) (s: outParam <| β -> β -> Prop) where
  protected map_rel (f: F) : ∀{a b: α}, r a b ↔ s (f a) (f b) := by intro f; exact f.map_rel

def map_rel₀ {F: Type*} [FunLike F α β] {r: α -> α -> Prop} {s: β -> β -> Prop} [IsRelMap F r s] (f: F) : ∀{a b: α}, r a b -> s (f a) (f b) :=
  IsRelMap.map_rel₀ f

def map_rel {F: Type*} [FunLike F α β] {r: α -> α -> Prop} {s: β -> β -> Prop} [IsRelHom F r s] (f: F) : ∀{a b: α}, r a b ↔ s (f a) (f b) :=
  IsRelHom.map_rel f

def map_rel_fwd {F: Type*} [FunLike F α β] {r: α -> α -> Prop} {s: β -> β -> Prop} [IsRelHom F r s] (f: F) : ∀{a b: α}, r a b -> s (f a) (f b) :=
  (map_rel f).mp

def map_rel_rev {F: Type*} [FunLike F α β] {r: α -> α -> Prop} {s: β -> β -> Prop} [IsRelHom F r s] (f: F) : ∀{a b: α}, s (f a) (f b) -> r a b :=
  (map_rel f).mpr

structure RelMap {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends Hom α β where
  protected map_rel₀ : ∀{a b: α}, r a b -> s (toFun a) (toFun b)

structure RelHom {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends Hom α β where
  protected map_rel : ∀{a b: α}, r a b ↔ s (toFun a) (toFun b)

structure RelEmbedding {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends α ↪ β, RelHom r s where

structure RelEquiv {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends α ≃ β, RelHom r s where

infixr:80 " →r₀ " => RelMap
infixr:80 " →r " => RelHom
infixr:80 " ↪r " => RelEmbedding
infixr:80 " ≃r " => RelEquiv

section

variable {α β γ: Type*} {r: α -> α -> Prop} {s: β -> β -> Prop} {t: γ -> γ -> Prop}

instance : FunLike (r →r₀ s) α β where
instance : IsRelMap (r →r₀ s) r s where

instance : FunLike (r →r s) α β where
instance : IsRelHom (r →r s) r s where

instance : EmbeddingLike (r ↪r s) α β where
instance : IsRelHom (r ↪r s) r s where

instance : EquivLike (r ≃r s) α β where
instance : IsRelHom (r ≃r s) r s where

def RelEmbedding.id (r: α -> α -> Prop) : r ↪r r where
  toEmbedding := Embedding.id _
  map_rel := Iff.rfl

def RelEmbedding.trans (f: r ↪r s) (g: s ↪r t) : r ↪r t where
  toEmbedding := f.toEmbedding.trans g.toEmbedding
  map_rel := Iff.trans (map_rel f) (map_rel g)

@[simp] def RelEmbedding.apply_toFun (f: r ↪r s) : f.toFun x = f x := rfl

def RelEquiv.id (r: α -> α -> Prop) : r ≃r r where
  toEquiv := Equiv.id _
  map_rel := Iff.rfl

def RelEquiv.comp (f: s ≃r t) (g: r ≃r s) : r ≃r t where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_rel := (map_rel g).trans (map_rel f)

def RelEquiv.trans (f: r ≃r s) (g: s ≃r t) : r ≃r t := RelEquiv.comp g f

def RelEquiv.symm (f: r ≃r s) : s ≃r r where
  toEquiv := f.toEquiv.symm
  map_rel := by
    intro a b
    rw (occs := [1]) [←f.symm_coe a, ←f.symm_coe b]
    apply (map_rel f).symm

def RelEquiv.toRelEmbedding (f: r ≃r s) : r ↪r s where
  toEmbedding := f.toEmbedding
  map_rel := map_rel f

@[simp] def RelEquiv.symm_coe (f: r ≃r s) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] def RelEquiv.coe_symm (f: r ≃r s) (x: α) : f.symm (f x) = x := f.rightInv _

end

namespace Relation

inductive ReflGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflGen R a a
| of (a b: α) : R a b -> ReflGen R a b

inductive ReflTransGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflTransGen R a a
| cons (a b c: α) : R a b -> ReflTransGen R b c -> ReflTransGen R a c

inductive EquivGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : EquivGen R a a
| symm {a b: α} : EquivGen R a b -> EquivGen R b a
| trans {a b c: α} : EquivGen R a b -> EquivGen R b c -> EquivGen R a c
| of {a b: α} : R a b -> EquivGen R a b

def ReflTransGen.trans : ReflTransGen R a b -> ReflTransGen R b c -> ReflTransGen R a c := by
  intro h g
  induction h generalizing c with
  | refl => assumption
  | cons _ _ _ _ _ ih =>
    apply ReflTransGen.cons
    assumption
    apply ih
    assumption

def ReflTransGen.of : R a b -> ReflTransGen R a b := by
  intro h; apply ReflTransGen.cons
  assumption
  apply ReflTransGen.refl

class IsRefl (R: α -> α -> Prop) where
  protected refl (a: α) : R a a

class IsSymm (R: α -> α -> Prop) where
  protected symm {a b: α} : R a b -> R b a

class IsTrans (R: α -> α -> Prop) where
  protected trans {a b c: α} : R a b -> R b c -> R a c

class IsAntisymm (R: α -> α -> Prop) (E: outParam (α -> α -> Prop)) where
  protected antisymm {a b: α} : R a b -> R b a -> E a b

class IsTotal (R: α -> α -> Prop) where
  protected total (a b: α) : R a b ∨ R b a

class IsTrichotomous (R: α -> α -> Prop) (E: outParam (α -> α -> Prop)) where
  protected trichotomous (a b: α) : R a b ∨ E a b ∨ R b a

class IsIrrefl (R: α -> α -> Prop) where
  protected irrefl {a: α} : ¬R a a

class IsAsymm (R: α -> α -> Prop) where
  protected asymm {a b: α} : R a b -> R b a -> False

class IsWelFounded (R: α -> α -> Prop) where
  protected wf : WellFounded R

class IsWellOrder (R: α -> α -> Prop) extends
  Relation.IsTrans R, Relation.IsWelFounded R, Relation.IsTrichotomous R (· = ·)


instance[Relation.IsTrans R] [Relation.IsWelFounded R] [Relation.IsTrichotomous R (· = ·)] : IsWellOrder R where

@[refl] def refl {R: α -> α -> Prop} [IsRefl R] (a: α) : R a a := IsRefl.refl _
def symm {R: α -> α -> Prop} [IsSymm R] {a b: α} : R a b -> R b a := IsSymm.symm
def trans {R: α -> α -> Prop} [IsTrans R] {a b c: α} : R a b -> R b c -> R a c := IsTrans.trans

def antisymm {R E: α -> α -> Prop} [IsAntisymm R E] {a b: α} : R a b -> R b a -> E a b := IsAntisymm.antisymm
def total (R: α -> α -> Prop) [IsTotal R]  (a b: α) : R a b ∨ R b a := IsTotal.total a b
def trichotomous (R: α -> α -> Prop) {E: outParam <| α -> α -> Prop} (a b: α) [IsTrichotomous R E] : R a b ∨ E a b ∨ R b a := IsTrichotomous.trichotomous a b
def irrefl {R: α -> α -> Prop} [IsIrrefl R] {a: α} : ¬R a a := IsIrrefl.irrefl
def asymm {R: α -> α -> Prop} [IsAsymm R] {a b: α} : R a b -> R b a -> False := IsAsymm.asymm
def wf (R: α -> α -> Prop) [IsWelFounded R] : WellFounded R := IsWelFounded.wf

def IsAntisymm.ofAsymm [IsAsymm R] : IsAntisymm R E where
  antisymm r s := nomatch asymm r s
def IsTrichotomous.ofTotal [IsTotal R] : IsTrichotomous R E where
  trichotomous a b :=
    match total R a b with
    | .inl x => .inl x
    | .inr x => .inr (.inr x)
instance [IsTrichotomous R (· = ·)] [IsRefl R] : IsTotal R where
  total a b := by
    rcases trichotomous R a b with h | rfl | h
    · left; assumption
    · left; rfl
    · right; assumption

instance [IsTrans R] [IsIrrefl R] : IsAsymm R where
  asymm a b := irrefl (trans a b)

instance [IsWelFounded R] : IsWelFounded (TransGen R) where
  wf := (wf R).transGen

instance [IsWelFounded R] : IsIrrefl R where
  irrefl {a} h := by
    induction a using (wf R).induction with
    | h a ih =>
    apply ih
    assumption
    assumption

instance : IsTrans (TransGen r) where
  trans := TransGen.trans
instance : IsTrans (ReflTransGen r) where
  trans := ReflTransGen.trans
instance : IsTrans (EquivGen r) where
  trans := EquivGen.trans

instance : IsRefl (ReflGen r) where
  refl := ReflGen.refl
instance : IsRefl (ReflTransGen r) where
  refl := ReflTransGen.refl
instance : IsRefl (EquivGen r) where
  refl := EquivGen.refl

instance : IsSymm (EquivGen r) where
  symm := EquivGen.symm

instance [IsWelFounded R] : IsAsymm R where
  asymm r s := asymm (TransGen.single r) (TransGen.single s)

instance : IsRefl (fun _ _: α => True) where
  refl _ := True.intro
instance : IsSymm (fun _ _: α => True) where
  symm := id
instance : IsTrans (fun _ _: α => False) where
  trans _ := id

instance : IsSymm (fun _ _: α => False) where
  symm := nofun
instance : IsAsymm (fun _ _: α => False) where
  asymm := nofun
instance : IsTrans (fun _ _: α => False) where
  trans := nofun

instance : @IsRefl α (· = ·) where
  refl := .refl
instance : @IsSymm α (· = ·) where
  symm := .symm
instance : @IsTrans α (· = ·) where
  trans := .trans

instance [s: Setoid α] : @IsRefl α (· ≈ ·) where
  refl := s.iseqv.refl
instance [s: Setoid α] : @IsSymm α (· ≈ ·) where
  symm := s.iseqv.symm
instance [s: Setoid α] : @IsTrans α (· ≈ ·) where
  trans := s.iseqv.trans

instance {s: β -> β -> Prop} [Relation.IsRefl s] (f: α -> β) : @IsRefl α (fun a b => s (f a) (f b)) where
  refl _ := Relation.refl _
instance {s: β -> β -> Prop} [Relation.IsSymm s] (f: α -> β) : @IsSymm α (fun a b => s (f a) (f b)) where
  symm := Relation.symm
instance {s: β -> β -> Prop} [Relation.IsTrans s] (f: α -> β) : @IsTrans α (fun a b => s (f a) (f b)) where
  trans := Relation.trans

def ofTransGen {R: α -> α -> Prop} {S: β -> β -> Prop} [IsTrans S] (f: R →r S) : TransGen R →r S where
  toFun := f
  map_rel := by
    intro a b
    apply Iff.intro
    · intro h
      induction h with
      | single =>
        apply map_rel_fwd _ (by assumption)
      | tail =>
        apply trans
        assumption
        apply map_rel_fwd f (by assumption)
    · intro h
      apply TransGen.single
      apply map_rel_rev f
      assumption

def ofReflTransGen {R: α -> α -> Prop} {S: β -> β -> Prop} [IsRefl S] [IsTrans S] (f: R →r S) : ReflTransGen R →r S where
  toFun := f
  map_rel := by
    intro a b
    apply Iff.intro
    · intro h
      induction h with
      | refl => rfl
      | cons _ _ _ h =>
        apply trans
        apply map_rel_fwd f (by assumption)
        assumption
    · intro h
      apply ReflTransGen.of
      apply map_rel_rev f
      assumption

def ofReflGen {R: α -> α -> Prop} {S: β -> β -> Prop} [IsRefl S] (f: R →r S) : ReflGen R →r S where
  toFun := f
  map_rel := by
    intro a b
    apply Iff.intro
    · intro h
      cases h with
      | refl => rfl
      | of _ h =>
        apply map_rel_fwd f (by assumption)
    · intro h
      apply ReflGen.of
      apply map_rel_rev f
      assumption

def ofEquivGen {R: α -> α -> Prop} {S: β -> β -> Prop} [IsRefl S] [IsTrans S] [IsSymm S] (f: R →r S) : EquivGen R →r S where
  toFun := f
  map_rel := by
    intro a b
    apply Iff.intro
    · intro h
      induction h with
      | refl => rfl
      | trans =>
        apply trans
        assumption
        assumption
      | symm =>
        apply symm
        assumption
      | of h =>
        apply map_rel_fwd f (by assumption)
    · intro h
      apply EquivGen.of
      apply map_rel_rev f
      assumption

def equiv (R: α -> α -> Prop) [IsRefl R] [IsTrans R] [IsSymm R] : Equivalence R where
  refl := refl
  symm := symm
  trans := trans

def setoid (R: α -> α -> Prop) [IsRefl R] [IsTrans R] [IsSymm R] : Setoid α where
  r := R
  iseqv := equiv R

section WellFounded

variable (R: α -> α -> Prop) [Relation.IsWelFounded R] {P: α -> Prop} (h: ∃a, P a)

def exists_min : ∃a, P a ∧ ∀b, R b a -> ¬P b := by
  obtain ⟨x, Pa⟩ := h
  induction x using (wf R).induction with
  | h a ih =>
  by_cases g:∃x, P x ∧ R x a
  · obtain ⟨x, Px, hx⟩ := g
    apply ih
    assumption
    assumption
  · refine ⟨a, Pa, ?_⟩
    intro x hx px
    apply g
    refine ⟨_, px, hx⟩

noncomputable def min : α := Classical.choose (exists_min R h)
def min_spec : P (min R h) := (Classical.choose_spec (exists_min R h)).left
def min_minimal : ∀a, R a (min R h) -> ¬P a := (Classical.choose_spec (exists_min R h)).right

attribute [irreducible] min

end WellFounded

end Relation

open Relation

variable {α β γ: Type*} {r: α -> α -> Prop} {s: β -> β -> Prop} {t: γ -> γ -> Prop}

def RelHom.liftTrans (f: r →r s) [Relation.IsTrans s] : Relation.IsTrans r where
  trans := by
    intro a b c h g
    exact map_rel_rev f <| trans (map_rel_fwd f h) (map_rel_fwd f g)
def RelHom.liftWellfounded (f: r →r s) [Relation.IsWelFounded s] : Relation.IsWelFounded r where
  wf := by
    apply WellFounded.intro
    intro a
    generalize hb:f a = b
    induction b using (wf s).induction generalizing a with
    | h b ih =>
    subst b
    apply Acc.intro
    intro b h
    exact ih _ (map_rel_fwd f h) _ rfl
def RelEmbedding.liftTrichotomous (f: r ↪r s) [Relation.IsTrichotomous s (· = ·)] : Relation.IsTrichotomous r (· = ·) where
  trichotomous a b := by
    rcases trichotomous s (f a) (f b) with h | h | h
    · exact .inl <| map_rel_rev f h
    · exact .inr <| .inl <| f.inj h
    · exact .inr <| .inr <| map_rel_rev f h
def RelEmbedding.liftWellOrder (f: r ↪r s) [Relation.IsWellOrder s] : Relation.IsWellOrder r := {
  f.toRelHom.liftTrans, f.toRelHom.liftWellfounded, f.liftTrichotomous with
}
def RelEmbedding.liftTotal (f: r ↪r s) [Relation.IsTotal s] : Relation.IsTotal r where
  total a b := by
    rcases total s (f a) (f b) with h | h
    · exact .inl <| map_rel_rev f h
    · exact .inr <| map_rel_rev f h

instance : @Relation.IsWellOrder ℕ (· < ·) where
  trans := Nat.lt_trans
  trichotomous := Nat.lt_trichotomy
  wf := Nat.lt_wfRel.wf

def Fin.relEmb : (fun a b: Fin n => a < b) ↪r (fun a b: Nat => a < b) where
  toFun := Fin.val
  inj _ _ := Fin.val_inj.mp
  map_rel := Iff.rfl

instance : @Relation.IsWellOrder (Fin n) (· < ·) := Fin.relEmb.liftWellOrder

def WellFounded.wrap (r: α -> α -> Prop) [Relation.IsWelFounded r] (a: α) : { x: α // Acc r x } := ⟨a, (Relation.wf r).apply _⟩

def Subtype.rel {P: α -> Prop} (r: α -> α -> Prop) : Subtype P -> Subtype P -> Prop := fun a b => r a b

def Subtype.relEmb (r: α -> α -> Prop) : rel (P := P) r ↪r r where
  toFun x := x.val
  inj := by
    intro ⟨a, _⟩ ⟨a, _⟩ h
    cases h
    rfl
  map_rel := Iff.rfl

instance [Relation.IsWelFounded r] : Relation.IsWelFounded (Subtype.rel (P := P) r) := (Subtype.relEmb r).liftWellfounded

instance [Relation.IsWelFounded r] : WellFoundedRelation { x: α // Acc r x } where
  rel := Subtype.rel r
  wf := Relation.wf (Subtype.rel (P := Acc r) r)

instance [Subsingleton α] [Relation.IsIrrefl r] : Relation.IsWellOrder r where
  trans := by
    intro a b c
    cases Subsingleton.allEq a b
    intro h
    nomatch Relation.irrefl h
  trichotomous _ _ := by
    right; left
    apply Subsingleton.allEq
  wf := by
    apply WellFounded.intro
    intro a
    apply Acc.intro
    intro b h
    rw [Subsingleton.allEq a b] at h
    nomatch Relation.irrefl h

instance : Relation.IsWelFounded (fun _ _: α => False) where
  wf := by
    apply WellFounded.intro
    intro a; apply Acc.intro
    nofun

instance (r: β -> β -> Prop) [Relation.IsWelFounded r] (f: α -> β) : Relation.IsWelFounded (fun a b => r (f a) (f b)) where
    wf := by
      apply WellFounded.intro
      intro a
      induction h:f a using (Relation.wf r).induction generalizing a with
      | _ x ih =>
      subst x
      apply Acc.intro
      intro b hb
      exact ih _ hb _ rfl


def Embedding.pullback_rel (r: β -> β -> Prop) (h: α ↪ β) (a b: α) : Prop := r (h a) (h b)
instance (r: β -> β -> Prop) [Relation.IsTrans r] (h: α ↪ β) : Relation.IsTrans (h.pullback_rel r) :=
  inferInstanceAs (Relation.IsTrans (fun a b => r (h a) (h b)))
instance (r: β -> β -> Prop) [Relation.IsWelFounded r] (f: α ↪ β) : Relation.IsWelFounded (f.pullback_rel r) :=
  inferInstanceAs (Relation.IsWelFounded (fun a b => r (f a) (f b)))
instance (r: β -> β -> Prop) [Relation.IsTrichotomous r (· = ·)] (f: α ↪ β) : Relation.IsTrichotomous (f.pullback_rel r) (· = ·) where
  trichotomous a b := by
    rcases Relation.trichotomous r (f a) (f b) with h | h | h
    · left; assumption
    · right; left; exact f.inj h
    · right; right; assumption
