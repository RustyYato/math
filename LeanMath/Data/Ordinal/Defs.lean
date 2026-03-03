import LeanMath.Tactic.PPWithUniv
import LeanMath.Logic.Relation.Defs

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

def type_in_ty (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) := { x: α // r x a }
def type_in_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) (x y: type_in_ty r a) : Prop := r x.val y.val

def type_in_rel_to_rel (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : type_in_rel r a ↪r r where
  toFun x := x.val
  inj := by intro a b h; cases a; cases b; cases h; rfl
  map_rel := Iff.rfl

instance {α: Type*} (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Relation.IsWellOrder (type_in_rel r a) :=
  (type_in_rel_to_rel r a).liftWellOrder
def type_in (r: α -> α -> Prop) [Relation.IsWellOrder r] (a: α) : Ordinal := type (type_in_rel r a)

end Ordinal
