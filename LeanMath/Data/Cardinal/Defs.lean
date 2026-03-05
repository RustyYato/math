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
def lift₂ (f: Type u -> Type v -> A) (h: ∀α₀ β₀ α₁ β₁, α₀ ≈ α₁ -> β₀ ≈ β₁ -> f α₀ β₀ = f α₁ β₁) : Cardinal -> Cardinal -> A
| .ofQuot a, .ofQuot b => a.lift₂ f h b

@[simp] def lift_type (f: Type u -> A) (h: ∀α β: Type u, α ≈ β -> f α = f β) (α: Type u) : lift f h (type α) = f α := rfl
@[simp] def lift₂_type (f: Type u -> Type v -> A) (h) (α: Type u) (β: Type v) : lift₂ f h (type α) (type β) = f α β := rfl

def sound (h: α ≃ β) : type α = type β := by
  show ofQuot _ = ofQuot _
  congr 1
  apply Quotient.sound
  exact ⟨h⟩

def exact (h: type α = type β) : α ≈ β := Quotient.exact (Cardinal.ofQuot.inj h)
noncomputable def exact' (h: type α = type β) : α ≃ β := Classical.choice (Quotient.exact (Cardinal.ofQuot.inj h))

instance : LE Cardinal where
  le := lift₂ (fun α β => Nonempty (α ↪ β)) <| by
    intro α₀ β₀ α₁ β₁ ⟨f⟩ ⟨g⟩
    dsimp
    simp; apply Iff.intro
    intro ⟨h⟩
    exact ⟨Equiv.embed_congr f g h⟩
    intro ⟨h⟩
    exact ⟨(Equiv.embed_congr f g).symm h⟩

instance : LT Cardinal where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder Cardinal where
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

end Cardinal
