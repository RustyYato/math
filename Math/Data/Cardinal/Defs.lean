module

public import Math.Data.Equiv.Defs
public import Math.Tactic.Basic

namespace Math

instance typeSetoid : Setoid (Type u) where
  r A B := Nonempty (A ≃ B)
  iseqv := {
    refl _ := ⟨.id _⟩
    symm | ⟨f⟩ => ⟨f.symm⟩
    trans | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩
  }

@[pp_with_univ]
public def Cardinal.{u} : Type (u + 1) := Quotient typeSetoid.{u}

namespace Cardinal

public def type (A: Type u) : Cardinal.{u} := Quotient.mk _ A
@[induction_eliminator] public theorem ind {motive: Cardinal.{u} -> Prop} (type: ∀(G: Type _), motive (type G)) (G: Cardinal) : motive G := Quotient.ind (fun G: Type u => type G) G
public def rec {motive: Cardinal -> Sort*} (type: ∀(G: Type u), motive (type G)) (h: ∀(A B: Type _), A ≃ B -> HEq (type A) (type B)) (G: Cardinal) : motive G := Quotient.hrecOn G (fun G: Type u => type G) <| by
  intro A B ⟨g⟩
  exact h _ _ g
public theorem sound {A B: Type u} : A ≃ B -> type A = type B := Quotient.sound ∘ Nonempty.intro
public def lift
  (f: Type u -> α)
  (hf: ∀(A B: Type u), A ≃ B -> f A = f B)
  (G: Cardinal.{u}) : α := Quotient.lift (fun G => f G) (by
    intro A B ⟨h⟩
    exact hf _ _ h) G
public def lift₂
  (f: Type u -> Type v -> α)
  (hf: ∀(A B C D), A ≃ C -> B ≃ D -> f A B = f C D)
  (A B: Cardinal) : α := Quotient.lift₂ (fun A B => f A B) (by
    intro A B C D ⟨h⟩ ⟨g⟩
    exact hf _ _ _ _ h g) A B
@[simp] public theorem lift_type (f: Type u -> α) (hf) (A: Type u) : lift f hf (type A) = f A := by rfl
@[simp] public theorem lift₂_type (f: Type u -> Type v -> α) (hf) (A: Type u) (B: Type v) : lift₂ f hf (type A) (type B) = f A B := by rfl

public theorem exists_rep (G: Cardinal) : ∃(A: Type u), type A = G := by
  induction G with | type A =>
  refine ⟨A, rfl⟩

end Cardinal
