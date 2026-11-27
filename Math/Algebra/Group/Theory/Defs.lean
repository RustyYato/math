module

public import Math.Algebra.Group.Defs.Basic

namespace Math

structure Group.Repr.{u} where
  Elem: Type u
  [ops: GroupOps Elem]
  [inst: IsGroup Elem]

attribute [coe] Group.Repr.Elem

instance : CoeSort Group.Repr.{u} (Type u) where
  coe := Group.Repr.Elem

instance (G: Group.Repr.{u}) : GroupOps G := G.ops
instance (G: Group.Repr.{u}) : IsGroup G := G.inst

instance groupSetoid : Setoid Group.Repr.{u} where
  r A B := Nonempty (A ≃* B)
  iseqv := {
    refl _ := ⟨.id _⟩
    symm | ⟨f⟩ => ⟨f.symm⟩
    trans | ⟨f⟩, ⟨g⟩ => ⟨f.trans g⟩
  }

section

@[pp_with_univ]
public def Group.{u} : Type (u + 1) := Quotient groupSetoid.{u}

namespace Group

public def type (G: Type*) [GroupOps G] [IsGroup G] : Group := Quotient.mk _ { Elem := G }
@[induction_eliminator] public theorem ind {motive: Group -> Prop} (type: ∀(G: Type _) [GroupOps G] [IsGroup G], motive (type G)) (G: Group) : motive G := Quotient.ind (fun G: Group.Repr => type G) G
public def rec {motive: Group -> Sort*} (type: ∀(G: Type _) [GroupOps G] [IsGroup G], motive (type G)) (h: ∀(A B: Type _) [GroupOps A] [IsGroup A] [GroupOps B] [IsGroup B], A ≃* B -> HEq (type A) (type B)) (G: Group) : motive G := Quotient.hrecOn G (fun G: Group.Repr => type G) <| by
  intro A B ⟨g⟩
  exact h _ _ g
public theorem sound (A B: Type u) [GroupOps A] [IsGroup A] [GroupOps B] [IsGroup B] : A ≃* B -> type A = type B := Quotient.sound ∘ Nonempty.intro
public def lift
  (f: ∀(G: Type u) [GroupOps G] [IsGroup G], α)
  (hf: ∀(A B: Type u) [GroupOps A] [IsGroup A] [GroupOps B] [IsGroup B], A ≃* B -> f A = f B)
  (G: Group.{u}) : α := Quotient.lift (fun G: Group.Repr => f G) (by
    intro A B ⟨h⟩
    exact hf _ _ h) G
public def lift₂
  (f: ∀(A: Type u) (B: Type v) [GroupOps A] [IsGroup A] [GroupOps B] [IsGroup B], α)
  (hf: ∀(A B C D) [GroupOps A] [IsGroup A] [GroupOps B] [IsGroup B] [GroupOps C] [IsGroup C] [GroupOps D] [IsGroup D], A ≃* C -> B ≃* D -> f A B = f C D)
  (A B: Group) : α := Quotient.lift₂ (fun A B: Group.Repr => f A B) (by
    intro A B C D ⟨h⟩ ⟨g⟩
    exact hf _ _ _ _ h g) A B
@[simp] public theorem lift_type (f: ∀(G: Type u) [GroupOps G] [IsGroup G], α) (hf) (A: Type u) [GroupOps A] [IsGroup A] : lift f hf (type A) = f A := by rfl
@[simp] public theorem lift₂_type (f: ∀(A: Type u) (B: Type v) [GroupOps A] [IsGroup A] [GroupOps B] [IsGroup B], α) (hf) (A: Type u) (B: Type v) [GroupOps A] [IsGroup A] [GroupOps B] [IsGroup B] : lift₂ f hf (type A) (type B) = f A B := by rfl

public theorem exists_rep (G: Group) : ∃(A: Type u) (_ops: GroupOps A) (_inst: IsGroup A), type A = G := by
  induction G with | type A =>
  refine ⟨A, inferInstance, inferInstance, rfl⟩

end Group
