module

public import Math.Order.Relation.Defs
public import Math.Tactic.Basic

namespace Math

structure WellOrder.{u} where
  Elem: Type u
  Rel: Elem -> Elem -> Prop
  [wo: IsWellOrder Rel]

instance WellOrder.setoid : Setoid WellOrder.{u} where
  r A B := Nonempty (A.Rel ≃r B.Rel)
  iseqv := {
    refl _ := ⟨.id _⟩
    symm | ⟨f⟩ => ⟨f.symm⟩
    trans | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩
  }

instance (O: WellOrder) : IsWellOrder O.Rel := O.wo

@[pp_with_univ]
public def Ordinal.{u} : Type (u + 1) := Quotient WellOrder.setoid.{u}

namespace Ordinal

public def type {A: Type u} (r: A -> A -> Prop) [IsWellOrder r] : Ordinal.{u} := Quotient.mk _ {
  Elem := _
  Rel := r
}
@[induction_eliminator] public theorem ind {motive: Ordinal.{u} -> Prop} (type: ∀{A: Type _} (r: A -> A -> Prop) [IsWellOrder r], motive (type r)) (G: Ordinal) : motive G := Quotient.ind (fun A: WellOrder => type A.Rel) G
public def rec {motive: Ordinal -> Sort*} (type: ∀{A: Type u} (r: A -> A -> Prop) [IsWellOrder r], motive (type r)) (h: ∀{A B: Type _} (r: A -> A -> Prop) (s: B -> B -> Prop) [IsWellOrder r] [IsWellOrder s], r ≃r s -> HEq (type r) (type s)) (G: Ordinal) : motive G := Quotient.hrecOn G (fun A: WellOrder => type A.Rel) <| by
  intro A B ⟨g⟩
  exact h _ _ g
public theorem sound {A B: Type u} {r: A -> A -> Prop} {s: B -> B -> Prop} [IsWellOrder r] [IsWellOrder s] : r ≃r s -> type r = type s := Quotient.sound ∘ Nonempty.intro
public def lift
  (f: ∀{A: Type u} (r: A -> A -> Prop) [IsWellOrder r], α)
  (hf: ∀{A B: Type u} (r: A -> A -> Prop) (s: B -> B -> Prop) [IsWellOrder r] [IsWellOrder s], A ≃ B -> f r = f s)
  (a: Ordinal.{u}) : α := Quotient.lift (fun A: WellOrder => f A.Rel) (by
    intro A B ⟨h⟩
    exact hf _ _ h) a
public def lift₂
  (f: ∀{A: Type u} {B: Type v} (r: A -> A -> Prop) (s: B -> B -> Prop) [IsWellOrder r] [IsWellOrder s], α)
  (hf: ∀{A: Type u} {B: Type v} {C: Type u} {D: Type v}
    (r₀: A -> A -> Prop) (s₀: B -> B -> Prop)
    (r₁: C -> C -> Prop) (s₁: D -> D -> Prop)
    [IsWellOrder r₀] [IsWellOrder s₀] [IsWellOrder r₁] [IsWellOrder s₁],
    r₀ ≃r r₁ -> s₀ ≃r s₁ -> f r₀ s₀ = f r₁ s₁)
  (a: Ordinal.{u}) (b: Ordinal.{v}) : α := Quotient.lift₂ (fun A B: WellOrder => f A.Rel B.Rel) (by
    intro A B C D ⟨h⟩ ⟨g⟩
    exact hf _ _ _ _ h g) a b
@[simp] public theorem lift_type
  (f: ∀{A: Type u} (r: A -> A -> Prop) [IsWellOrder r], α)
  (hf) (A: Type u) (r: A -> A -> Prop) [IsWellOrder r] : lift f hf (type r) = f r := by rfl
@[simp] public theorem lift₂_type
  (f: ∀{A: Type u} {B: Type v} (r: A -> A -> Prop) (s: B -> B -> Prop) [IsWellOrder r] [IsWellOrder s], α)
  (hf) (A: Type u) (B: Type v) (r: A -> A -> Prop) (s: B -> B -> Prop) [IsWellOrder r] [IsWellOrder s] : lift₂ f hf (type r) (type s) = f r s := by rfl

end Ordinal
