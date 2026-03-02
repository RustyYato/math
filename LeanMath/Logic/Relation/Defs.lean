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

structure RelEmbedding {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends α ↪ β where
  protected map_rel : ∀{a b: α}, r a b ↔ s (toFun a) (toFun b)

structure RelEquiv {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends α ≃ β where
  protected map_rel : ∀{a b: α}, r a b ↔ s (toFun a) (toFun b)

infixr:80 " →r₀ " => RelMap
infixr:80 " →r " => RelHom
infixr:80 " ↪r " => RelEmbedding
infixr:80 " ≃r " => RelEquiv

section

variable {α β: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop)

instance : FunLike (r →r₀ s) α β where
instance : IsRelMap (r →r₀ s) r s where

instance : FunLike (r →r s) α β where
instance : IsRelHom (r →r s) r s where

instance : FunLike (r ↪r s) α β where
instance : IsRelHom (r ↪r s) r s where

instance : FunLike (r ≃r s) α β where
instance : IsRelHom (r ≃r s) r s where

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

def ofTransGen {R: α -> α -> Prop} {S: β -> β -> Prop} [IsTrans S] (f: R →r S) : TransGen R →r S where
  toFun := f
  map_rel := by
    intro a b
    apply Iff.intro
    · intro h
      induction h with
      | single =>
        apply map_rel_fwd
        assumption
      | tail =>
        apply trans
        assumption
        apply map_rel_fwd f
        assumption
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
        apply map_rel_fwd f
        assumption
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
        apply map_rel_fwd f
        assumption
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
        apply map_rel_fwd f
        assumption
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
