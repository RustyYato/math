import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Ring.Order
import LeanMath.Algebra.Semifield.Order
import LeanMath.Algebra.Norm.Basic
import LeanMath.Tactic.AxiomBlame

section

namespace CauchySeq

def Eventually (P: ℕ -> Prop) : Prop := ∃k, ∀i, k ≤ i -> P i
def Eventually₂ (P: ℕ -> ℕ -> Prop) : Prop := ∃k, ∀i j, k ≤ i -> k ≤ j -> P i j

def Eventually₂.merge₂
  {P Q: ℕ -> ℕ -> Prop} (h: Eventually₂ P) (g: Eventually₂ Q) : Eventually₂ fun i j => P i j ∧ Q i j := by
  obtain ⟨k₀, hk₀⟩ := h
  obtain ⟨k₁, hk₁⟩ := g
  exists k₀ ⊔ k₁
  intro i j hi hj
  apply And.intro
  apply hk₀
  apply le_trans _ hi
  apply left_le_max
  apply le_trans _ hj
  apply left_le_max
  apply hk₁
  apply le_trans _ hi
  apply right_le_max
  apply le_trans _ hj
  apply right_le_max

end CauchySeq

variable {α γ: Type*} [Norm α γ] [LE γ] [LT γ] [IsLinearOrder γ]
  [RingOps α] [IsRing α]
  [FieldOps γ] [IsField γ]

def is_cauchy_eqv (f g: ℕ -> α) : Prop :=
  ∀ε: γ, 0 < ε -> CauchySeq.Eventually₂ (fun i j => ‖f i - g j‖ < ε)

def is_cauchy (f: ℕ -> α) : Prop := is_cauchy_eqv f f

structure CauchySeq (α γ: Type*)
  [Norm α γ] [LE γ] [LT γ] [IsLinearOrder γ]
  [RingOps α] [IsRing α]
  [FieldOps γ] [IsField γ] where
  toFun : ℕ -> α
  protected is_cauchy': is_cauchy toFun

variable
  [Norm γ γ] [SMul γ α]
  [IsLawfulAbs γ] [IsLawfulNorm α γ]
  [IsStrictOrderedSemiring γ] [IsZeroNeOne γ]
  [IsDistributiveAction γ α]
  [IsLeftDistribSMul γ α]
  [IsLawfulZeroSMul γ α]
  [IsZeroLEOne γ]

local macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply natCast_ne_zero)

private def half_pos {a: γ} (h: 0 < a) : 0 < a /? (2: ℕ) := pos_div?_natCast h 1

namespace CauchySeq

instance : FunLike (CauchySeq α γ) ℕ α where

protected def is_cauchy (c: CauchySeq α γ) : is_cauchy c := c.is_cauchy'

instance setoid : Setoid (CauchySeq α γ) where
  r a b := is_cauchy_eqv a b
  iseqv := {
    refl a := a.is_cauchy
    symm := by
      intro a b h
      intro ε hε
      have ⟨k, hk⟩ := h ε hε
      exists k
      intro i j hi hj
      rw [norm_sub]
      apply hk <;> assumption
    trans {x y z} h g := by
      intro ε εpos
      replace h := h _ (half_pos (half_pos εpos))
      replace g := g _ (half_pos (half_pos εpos))
      replace c := y.is_cauchy _ (half_pos εpos)
      replace h := (h.merge₂ g).merge₂ c; clear g c
      obtain ⟨k, h⟩ := h
      exists k
      intro i j hi hj
      replace ⟨⟨h, g⟩, c⟩ := h i j hi hj
      rw [norm_sub] at c
      have := lt_of_le_of_lt (norm_add_le_add_norm _ _) (add_lt_add h g)
      replace := lt_of_le_of_lt (norm_add_le_add_norm _ _) (add_lt_add this c)
      clear h g c
      rwa [half_add_half, half_add_half,
        sub_add_assoc, ←add_sub_assoc (-_),
        add_comm (-_), ←sub_eq_add_neg,
        sub_eq_add_neg _ (z j),
        add_comm _ (-z j), ←add_assoc,
        ←sub_eq_add_neg, add_assoc,
        ←neg_sub (y i),  add_neg_cancel,
        add_zero] at this
  }

structure Completion (α γ: Type*)
  [Norm α γ] [LE γ] [LT γ] [IsLinearOrder γ]
  [RingOps α] [IsRing α]
  [FieldOps γ] [IsField γ]
  [Norm γ γ] [SMul γ α]
  [IsLawfulAbs γ] [IsLawfulNorm α γ]
  [IsStrictOrderedSemiring γ] [IsZeroNeOne γ]
  [IsDistributiveAction γ α]
  [IsLeftDistribSMul γ α]
  [IsLawfulZeroSMul γ α]
  [IsZeroLEOne γ] where
  ofQuot :: toQuot : Quotient (setoid (α := α))

def const (a: α) : CauchySeq α γ where
  toFun _ := a
  is_cauchy' := by
    intro ε h
    exists 0; intros
    simpa [sub_self]

@[simp] def apply_const (a: α) (i: ℕ) : CauchySeq.const a i = a := rfl

def ofSeq (c: CauchySeq α γ) : Completion α γ where
  toQuot := Quotient.mk _ c

def sound {a b: CauchySeq α γ} : a ≈ b -> ofSeq a = ofSeq b := by
  intro h; have := Quotient.sound h
  unfold ofSeq; congr

def exact {a b: CauchySeq α γ} : ofSeq a = ofSeq b -> a ≈ b := by
  intro h
  exact Quotient.exact (Completion.ofQuot.inj h)

@[induction_eliminator]
def ind {motive: Completion α γ -> Prop} (ofSeq : ∀c, motive (ofSeq c)) (c: Completion α γ) : motive c := by
  obtain ⟨c⟩ := c
  induction c using Quotient.ind
  apply ofSeq

def lift (f: CauchySeq α γ -> β) (h: ∀a b, a ≈ b -> f a = f b) (c: Completion α γ) : β :=
  c.toQuot.lift f h
def lift₂ (f: CauchySeq α γ -> CauchySeq α γ -> β) (h: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: Completion α γ) : β :=
  a.toQuot.liftOn₂ b.toQuot f h

@[simp] def lift_ofSeq (f: CauchySeq α γ -> β) (h) (a: CauchySeq α γ) : lift f h (ofSeq a) = f a := rfl
@[simp] def lift₂_ofSeq (f: CauchySeq α γ -> CauchySeq α γ -> β) (h) (a b: CauchySeq α γ) : lift₂ f h (ofSeq a) (ofSeq b) = f a b := rfl

def Completion.const : α -> Completion α γ := ofSeq ∘ .const

def Completion.const_inj [DecidableEq α] : Function.Injective (const (α := α)) := by
  intro a b h
  replace h := exact h
  apply Decidable.byContradiction; intro g
  have ⟨k, hk⟩ := h ‖a - b‖ ?_
  have := hk k k (Nat.le_refl _) (Nat.le_refl _)
  dsimp at this
  exact Relation.irrefl this
  apply lt_of_le_of_ne
  apply norm_nonneg
  intro h
  have := (sub_eq_zero _ _).mpr (of_norm_eq_zero h.symm)
  contradiction

end CauchySeq

end
