import LeanMath.Tactic.PPWithUniv
import LeanMath.Tactic.AxiomBlame
import LeanMath.Data.Equiv.Antisymm
import LeanMath.Data.Equiv.Basic
import LeanMath.Order.Defs

instance Type.instSetoid : Setoid (Type u) where
  r a b := Nonempty (a ≃ b)
  iseqv := {
    refl _ := ⟨.id _⟩
    symm := fun ⟨h⟩ => ⟨h.symm⟩
    trans := fun ⟨h⟩ ⟨g⟩ => ⟨h.trans g⟩
  }

@[pp_with_univ]
structure Cardinal.{u} where
  ofQuot :: toQuot : Quotient Type.instSetoid.{u}

namespace Cardinal

def type (α: Type u) : Cardinal.{u} where
  toQuot := Quotient.mk _ α

@[cases_eliminator]
def ind {motive: Cardinal -> Prop} (type: ∀α, motive (type α)) (c: Cardinal) : motive c := by
  cases c with | ofQuot c =>
  induction c using Quotient.ind with | _ c =>
  apply type

def lift (f: Type u -> A) (h: ∀α β: Type u, α ≈ β -> f α = f β) : Cardinal -> A
| .ofQuot c => c.lift f h
def lift₂ (f: Type u -> Type v -> A) (h: ∀α₀ β₀ α₁ β₁, (α₀ ≃ α₁) -> (β₀ ≃ β₁) -> f α₀ β₀ = f α₁ β₁) : Cardinal -> Cardinal -> A
| .ofQuot a, .ofQuot b => a.liftOn₂ b f (fun a b c d ⟨h₀⟩ ⟨h₁⟩ => h a b c d h₀ h₁)

@[simp] def lift_type (f: Type u -> A) (h: ∀α β: Type u, α ≈ β -> f α = f β) (α: Type u) : lift f h (type α) = f α := rfl
@[simp] def lift₂_type (f: Type u -> Type v -> A) (h) (α: Type u) (β: Type v) : lift₂ f h (type α) (type β) = f α β := rfl

def sound (h: α ≃ β) : type α = type β := by
  show ofQuot _ = ofQuot _
  congr 1
  apply Quotient.sound
  exact ⟨h⟩

def exact (h: type α = type β) : α ≈ β := Quotient.exact (Cardinal.ofQuot.inj h)
noncomputable def exact' (h: type α = type β) : α ≃ β := Classical.choice (Quotient.exact (Cardinal.ofQuot.inj h))

instance : LE Cardinal.{u} where
  le := lift₂ (fun α β => Nonempty (α ↪ β)) <| by
    intro α₀ β₀ α₁ β₁ f g
    dsimp
    simp; apply Iff.intro
    intro ⟨h⟩
    exact ⟨Equiv.embed_congr f g h⟩
    intro ⟨h⟩
    exact ⟨(Equiv.embed_congr f g).symm h⟩

instance : LT Cardinal.{u} where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder Cardinal.{u} where
  lt_iff_le_and_not_ge := Iff.rfl
  refl x := by
    cases x
    exact ⟨Embedding.id _⟩
  trans := by
    intro a b c h g
    cases a with | _ α =>
    cases b with | _ β =>
    cases c with | _ γ =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    exact ⟨h.trans g⟩
  antisymm := by
    intro a b
    cases a with | _ α =>
    cases b with | _ β =>
    intro ⟨f⟩ ⟨g⟩
    apply sound
    apply Equiv.antisymm
    assumption
    assumption

instance : Add Cardinal.{u} where
  add := lift₂ (type <|· ⊕ ·) <| by
    intro _ _ _ _ h g
    apply sound
    apply Equiv.sum_congr
    assumption
    assumption

instance : Mul Cardinal.{u} where
  mul := lift₂ (type <|· × ·) <| by
    intro _ _ _ _ h g
    apply sound
    apply Equiv.prod_congr
    assumption
    assumption

instance : Pow Cardinal.{u} Cardinal.{u} where
  pow := lift₂ (fun α β => type <| β -> α) <| by
    intro _ _ _ _ h g
    apply sound
    apply Equiv.fun_congr
    assumption
    assumption

def ofNat (n: ℕ) : Cardinal := type (Fin n)

def ulift.{v, u} : Cardinal.{u} -> Cardinal.{max u v} :=
  lift (fun x => type (ULift x)) <| by
    intro α β ⟨h⟩
    apply sound
    exact Equiv.ulift_congr h

instance : NatCast Cardinal.{u} where
  natCast n := ulift (ofNat n)

instance : Pow Cardinal ℕ where
  pow a n := a ^ (n: Cardinal)

instance : SMul ℕ Cardinal.{u} where
  smul n a := n * a

instance : OfNat Cardinal n := ⟨n⟩

def exists_eq_type (c: Cardinal.{u}) : ∃α: Type u, type α = c := by
  cases c
  exact ⟨_, rfl⟩
def out (c: Cardinal.{u}) : Type u := Classical.choose c.exists_eq_type
def out_spec (c: Cardinal.{u}) : type c.out = c := Classical.choose_spec c.exists_eq_type

def sum {ι: Type v} (f: ι -> Cardinal.{u}) : Cardinal.{max v u} := type (Σi, (f i).out)
def prod {ι: Type v} (f: ι -> Cardinal.{u}) : Cardinal.{max v u} := type (∀i, (f i).out)

end Cardinal
