import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Ring.Order
import LeanMath.Algebra.Semifield.Order
import LeanMath.Algebra.Norm.Basic
import LeanMath.Algebra.Algebra.Defs
import LeanMath.Algebra.Module.Defs
import LeanMath.Data.Fintype.Order
import LeanMath.Tactic.AxiomBlame

variable {α β γ: Type*}
-- variable [DecidableEq α]

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

def Eventually.merge
  {P Q: ℕ -> Prop} (h: Eventually P) (g: Eventually Q) : Eventually fun i => P i ∧ Q i := by
  obtain ⟨k₀, hk₀⟩ := h
  obtain ⟨k₁, hk₁⟩ := g
  exists k₀ ⊔ k₁
  intro i hi
  apply And.intro
  apply hk₀
  apply le_trans _ hi
  apply left_le_max
  apply hk₁
  apply le_trans _ hi
  apply right_le_max

def Eventually₂.merge
  {P: ℕ -> ℕ -> Prop} {Q: ℕ -> Prop} (h: Eventually₂ P) (g: Eventually Q) : Eventually₂ fun i j => P i j ∧ Q i := by
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

end CauchySeq

section

variable [Norm α γ] [Norm β γ] [LE γ] [LT γ] [IsLinearOrder γ]
  [FieldOps α] [IsField α] [FieldOps β] [IsField β]
  [FieldOps γ] [IsField γ]

def is_cauchy_eqv (f g: ℕ -> α) : Prop :=
  ∀ε: γ, 0 < ε -> CauchySeq.Eventually₂ (fun i j => ‖f i - g j‖ < ε)

def is_cauchy (f: ℕ -> α) : Prop := is_cauchy_eqv f f

structure CauchySeq (α γ: Type*)
  [Norm α γ] [LE γ] [LT γ] [IsLinearOrder γ]
  [FieldOps α] [IsField α]
  [FieldOps γ] [IsField γ] where
  toFun : ℕ -> α
  protected is_cauchy': is_cauchy toFun

end

protected class CauchySeq.MetricFieldOps (γ: Type*) extends FieldOps γ, LE γ, LT γ, Max γ, Norm γ γ where

protected class CauchySeq.IsMetricField (γ: Type*)
  [CauchySeq.MetricFieldOps γ] : Prop
  extends
  IsField γ,
  IsLinearOrder γ, IsSemiLatticeMax γ,
  IsZeroLEOne γ, IsStrictOrderedSemiring γ,
  IsLawfulAbs γ, IsAbsMax γ
  where

instance
  (priority := 1)
  CauchySeq.isntMetricFieldOps
  [LE γ] [LT γ] [FieldOps γ] [Norm γ γ] [Max γ]
  : CauchySeq.MetricFieldOps γ where

instance
  (priority := 1)
  CauchySeq.instIsMetricField
  [CauchySeq.MetricFieldOps γ]
  [IsLinearOrder γ] [IsField γ]
  [IsZeroLEOne γ] [IsStrictOrderedSemiring γ]
  [IsSemiLatticeMax γ] [IsLawfulAbs γ] [IsAbsMax γ]
  : CauchySeq.IsMetricField γ where

-- private class VectorSpaceOps (α: Type*) (γ: outParam Type*) [MetricField γ] [FieldOps α] [IsField α] [Norm α γ]
--   extends SMul γ α, IsLawfulNorm α γ,
--     IsDistributiveAction γ α, IsLeftDistribSMul γ α, IsLawfulZeroSMul γ α where

protected class CauchySeq.VectorSpaceOps (α: Type*) (γ: outParam Type*) [CauchySeq.MetricFieldOps γ] [FieldOps α] extends Norm α γ, SMul γ α where

protected class CauchySeq.IsVectorSpace (α γ: Type*) [CauchySeq.MetricFieldOps γ] [CauchySeq.IsMetricField γ] [FieldOps α] [IsField α] [CauchySeq.VectorSpaceOps α γ]
  : Prop extends IsLawfulNorm α γ, IsDistributiveAction γ α, IsLeftDistribSMul γ α, IsLawfulZeroSMul γ α where

instance
  (priority := 1)
  CauchySeq.instVectorSpaceOps
  [CauchySeq.MetricFieldOps γ] [FieldOps α]
  [Norm α γ] [SMul γ α] : CauchySeq.VectorSpaceOps α γ where

instance
  (priority := 1)
  CauchySeq.instIsVectorSpace
  [CauchySeq.MetricFieldOps γ] [CauchySeq.IsMetricField γ] [FieldOps α] [IsField α]
  [CauchySeq.VectorSpaceOps α γ]
  [IsLawfulNorm α γ]
  [IsDistributiveAction γ α] [IsLeftDistribSMul γ α]
  [IsLawfulZeroSMul γ α] : CauchySeq.IsVectorSpace α γ where

section

variable
  [CauchySeq.MetricFieldOps γ] [CauchySeq.IsMetricField γ]
  [FieldOps α] [IsField α] [FieldOps β] [IsField β]
  [CauchySeq.VectorSpaceOps α γ] [CauchySeq.VectorSpaceOps β γ]
  [CauchySeq.IsVectorSpace α γ] [CauchySeq.IsVectorSpace β γ]

local macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply natCast_ne_zero)

private def half_pos {a: γ} (h: 0 < a) : 0 < a /? (2: ℕ) := pos_div?_natCast h 1

def safe_inv [DecidableEq α] (a: ℕ -> α) (i: ℕ): α :=
  if hb:a i = 0 then 0 else (a i)⁻¹?

def is_cauchy_eqv.add
  {a b c d: ℕ -> α}
  (ac: is_cauchy_eqv a c)
  (bd: is_cauchy_eqv b d) :
  is_cauchy_eqv (fun i => a i + b i) (fun i => c i + d i) := by
  intro ε εpos
  replace ac := ac _ (half_pos εpos)
  replace bd := bd _ (half_pos εpos)
  have ⟨k, h⟩ := ac.merge₂ bd; clear ac bd
  exists k; intro i j hi hj
  dsimp; obtain ⟨ac, bd⟩ := h i j hi hj
  clear h; rw [add_comm (c j), sub_add, add_sub_comm, add_sub_assoc]
  apply lt_of_le_of_lt
  apply norm_add_le_add_norm
  rw [←half_add_half ε]
  apply add_lt_add
  assumption
  assumption

def is_cauchy_eqv.neg
  {a b: ℕ -> α}
  (h: is_cauchy_eqv a b) :
  is_cauchy_eqv (fun i => -a i) (fun i => -b i) := by
  intro ε εpos
  have ⟨k, hk⟩ := h ε εpos
  exists k; intro i j hi hj
  replace hk := hk i j hi hj
  dsimp at hk; dsimp
  rwa [sub_eq_add_neg, neg_neg, add_comm, ←sub_eq_add_neg,
    norm_sub]

def is_cauchy_eqv.norm {a b: ℕ -> α} (h: is_cauchy_eqv a b) :
  is_cauchy_eqv (fun i => ‖a i‖) (fun i => ‖b i‖) := by
  intro ε εpos
  obtain ⟨k, hk⟩ := h _ εpos
  exists k; intro i j hi hj
  replace hk := hk i j hi hj; dsimp at *
  apply lt_of_le_of_lt _ hk
  have v₀ := norm_add_le_add_norm (a i - b j) (b j)
  rw [sub_add_assoc, neg_add_cancel, add_zero] at v₀
  replace v₀ := le_add_iff_sub_le.mp v₀
  have v₁ := norm_add_le_add_norm (b j - a i) (a i)
  rw [sub_add_assoc, neg_add_cancel, add_zero] at v₁
  replace v₁ := le_add_iff_sub_le.mp v₁
  rw [norm_sub] at v₁
  rw [abs_eq_max]
  apply max_le
  assumption
  rw [neg_sub]
  assumption

def bounded_difference {a b: ℕ -> α} (h: is_cauchy_eqv a b) : ∃B, ∀i, ‖a i - b i‖ < B := by
  have ⟨k, hk⟩ := h 1 (zero_lt_one _)
  let max := max_of_range_with (fun i: Fin k => ‖a i - b i‖) 1
  exists max + 1
  intro i
  rcases lt_or_le i k with g | g
  · apply lt_of_le_of_lt _
    show max < max +1
    rw (occs := [1]) [←add_zero max]
    apply add_lt_add_left
    apply zero_lt_one; simp [max]
    apply le_max_of_range_with (i := ⟨i, g⟩) (f := fun i: Fin k => ‖a i - b i‖)
  · apply lt_of_lt_of_le
    apply hk
    assumption
    assumption
    apply le_add_left
    simp [max]
    apply le_trans
    apply zero_le_one
    apply bot_le_max_of_range_with

end

namespace CauchySeq

section

variable
  [CauchySeq.MetricFieldOps γ] [CauchySeq.IsMetricField γ]
  [FieldOps α] [IsField α] [FieldOps β] [IsField β]
  [CauchySeq.VectorSpaceOps α γ] [CauchySeq.VectorSpaceOps β γ]
  [CauchySeq.IsVectorSpace α γ] [CauchySeq.IsVectorSpace β γ]

instance : FunLike (CauchySeq α γ) ℕ α where

protected def is_cauchy (c: CauchySeq α γ) : is_cauchy c := c.is_cauchy'

def symm : ∀{f g: ℕ -> α}, is_cauchy_eqv f g -> is_cauchy_eqv g f := by
  intro a b h
  intro ε hε
  have ⟨k, hk⟩ := h ε hε
  exists k
  intro i j hi hj
  rw [norm_sub]
  apply hk <;> assumption

def trans : ∀{a b c: ℕ -> α}, is_cauchy_eqv b b -> is_cauchy_eqv a b -> is_cauchy_eqv b c -> is_cauchy_eqv a c := by
  intro x y z hb h g
  intro ε εpos
  replace h := h _ (half_pos (half_pos εpos))
  replace g := g _ (half_pos (half_pos εpos))
  replace c := hb _ (half_pos εpos)
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

instance setoid : Setoid (CauchySeq α γ) where
  r a b := is_cauchy_eqv a b
  iseqv := {
    refl a := a.is_cauchy
    symm {x y} := by
      apply symm
    trans {x y z} h g := by
      apply trans
      exact y.is_cauchy
      assumption
      assumption
  }

def bounded (c: CauchySeq α γ) : ∃B, ∀i, ‖c i‖ < B := by
  have ⟨k, hk⟩ := c.is_cauchy 1 (zero_lt_one _)
  let max := max_of_range_with (fun i: Fin k => ‖c i.val‖) 1
  exists max + (‖c k‖ + 1)
  intro i
  rcases lt_or_le i k with h | h
  · apply lt_of_le_of_lt _
    show max < max + (‖c k‖ + 1); rw (occs := [1]) [←add_zero max]
    apply add_lt_add_left
    apply lt_of_lt_of_le
    exact zero_lt_one _
    apply le_add_left
    apply norm_nonneg
    apply le_max_of_range_with (i := ⟨i ,h⟩) (fun i: Fin k => ‖c i‖)
  · replace hk := hk i k h (Nat.le_refl _); dsimp at hk
    rw [add_comm ‖_‖, ←add_assoc]
    apply lt_add_iff_sub_lt.mpr
    apply lt_of_lt_of_le _
    apply le_add_left
    apply le_trans (zero_le_one _)
    apply bot_le_max_of_range_with
    apply lt_of_le_of_lt _ hk
    apply sub_le_iff_le_add.mpr
    apply le_trans _ (norm_add_le_add_norm _ _)
    rw [sub_add_assoc, neg_add_cancel, add_zero]

def bounded_with (c: CauchySeq α γ) (lb: γ) : ∃B, lb < B ∧ ∀i, ‖c i‖ < B := by
  have ⟨B, hB⟩  := c.bounded
  exists B ⊔ (lb + 1)
  apply And.intro
  apply lt_of_lt_of_le _ right_le_max
  rw (occs := [1]) [←add_zero lb]
  apply add_lt_add_left
  exact zero_lt_one _
  intro i
  apply lt_of_lt_of_le _ left_le_max
  apply hB

def _root_.is_cauchy_eqv.mul
  [IsLawfulMulNorm α γ]
  (a b c d: CauchySeq α γ)
  (ac: a ≈ c)
  (bd: b ≈ d) :
  is_cauchy_eqv (fun i => a i * b i) (fun i => c i * d i) := by
  have ⟨Ba, Ba_pos, hBa⟩ := a.bounded_with 0
  have ⟨Bd, Bd_pos, hBd⟩ := d.bounded_with 0
  intro ε εpos
  let ε₀ := ε /? (2: ℕ) /? Bd
  let ε₁ := ε /? (2: ℕ) /? Ba
  have hε₀ : 0 < ε₀ := by
    apply pos_div?
    apply half_pos
    assumption
    assumption
  have hε₁ : 0 < ε₁ := by
    apply pos_div?
    apply half_pos
    assumption
    assumption

  replace ⟨k, hk⟩ := (ac _ hε₀).merge₂ (bd _ hε₁)
  exists k; intro i j hi hj; dsimp
  replace ⟨ac, bd⟩ := hk i j hi hj
  rw [←add_zero (a i * _),
    ←neg_add_cancel (a i * d j), neg_mul_right,
    ←add_assoc, add_sub_assoc, ←mul_add, ←sub_mul,
    ←sub_eq_add_neg, ←half_add_half ε]
  apply lt_of_le_of_lt
  apply norm_add_le_add_norm
  apply add_lt_add
  · rw [norm_mul]
    apply lt_of_le_of_lt
    apply mul_le_mul_of_nonneg_right
    apply le_of_lt; apply hBa
    apply norm_nonneg
    apply lt_of_mul_lt_mul_of_pos_left
    exact pos_inv? _ Ba_pos
    rw [←mul_assoc, inv?_mul_cancel, one_mul, mul_comm _, ←div?_eq_mul_inv?]
    assumption
  · rw [norm_mul]
    apply lt_of_le_of_lt
    apply mul_le_mul_of_nonneg_left
    apply le_of_lt; apply hBd
    apply norm_nonneg
    apply lt_of_mul_lt_mul_of_pos_right
    exact pos_inv? _ Bd_pos
    rw [mul_assoc, mul_inv?_cancel, mul_one, ←div?_eq_mul_inv?]
    assumption

end

structure Completion (α γ: Type*)
  [LE γ] [LT γ] [IsLinearOrder γ]
  [FieldOps γ] [IsField γ] [Norm γ γ]
  [IsZeroLEOne γ] [IsStrictOrderedSemiring γ]
  [Max γ] [IsSemiLatticeMax γ] [IsLawfulAbs γ] [IsAbsMax γ]

  [FieldOps α] [IsField α]
  [Norm α γ] [SMul γ α] [IsLawfulNorm α γ]
  [IsDistributiveAction γ α] [IsLeftDistribSMul γ α]
  [IsLawfulZeroSMul γ α]
  where
  ofQuot :: toQuot : Quotient (setoid (α := α))

variable
  [CauchySeq.MetricFieldOps γ] [CauchySeq.IsMetricField γ]
  [FieldOps α] [IsField α] [FieldOps β] [IsField β]
  [CauchySeq.VectorSpaceOps α γ] [CauchySeq.VectorSpaceOps β γ]
  [CauchySeq.IsVectorSpace α γ] [CauchySeq.IsVectorSpace β γ]

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

def lift (f: CauchySeq α γ -> Γ) (h: ∀a b, a ≈ b -> f a = f b) (c: Completion α γ) : Γ :=
  c.toQuot.lift f h
def lift₂ (f: CauchySeq α γ -> CauchySeq β γ -> Γ) (h: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a: Completion α γ) (b: Completion β γ) : Γ :=
  a.toQuot.liftOn₂ b.toQuot f h

@[simp] def lift_ofSeq (f: CauchySeq α γ -> Γ) (h) (a: CauchySeq α γ) : lift f h (ofSeq a) = f a := rfl
@[simp] def lift₂_ofSeq (f: CauchySeq α γ -> CauchySeq β γ -> Γ) (h) (a: CauchySeq α γ) (b: CauchySeq β γ) : lift₂ f h (ofSeq a) (ofSeq b) = f a b := rfl

@[ext] def ext (a b: CauchySeq α γ) (h: ∀i, a i = b i) : a = b := DFunLike.ext a b h
def copy (c: CauchySeq α γ) (f: ℕ -> α) (hf: ∀i, c i = f i) : CauchySeq α γ where
  toFun := f
  is_cauchy' := by
    rw [←funext hf]
    exact c.is_cauchy'

def copy_eq (c: CauchySeq α γ) (f: ℕ -> α) (hf: ∀i, c i = f i) : c.copy f hf = c := by
  ext; symm; apply hf

def Completion.const : α -> Completion α γ := ofSeq ∘ .const

def Completion.const_inj [ExcludedMiddleEq α] : Function.Injective (const (α := α)) := by
  intro a b h
  replace h := exact h
  apply LEM.byContradiction; intro g
  have ⟨k, hk⟩ := h ‖a - b‖ ?_
  have := hk k k (Nat.le_refl _) (Nat.le_refl _)
  dsimp at this
  exact Relation.irrefl this
  apply lt_of_le_of_ne
  apply norm_nonneg
  intro h
  have := (sub_eq_zero _ _).mpr (of_norm_eq_zero h.symm)
  contradiction

instance : Add (CauchySeq α γ) where
  add a b := {
    toFun i := a i + b i
    is_cauchy' := by
      apply is_cauchy_eqv.add
      exact a.is_cauchy
      exact b.is_cauchy
  }

instance : Add (Completion α γ) where
  add := lift₂ (fun a b => ofSeq (a + b)) <| by
    intro a b c d ac bd
    apply sound
    apply is_cauchy_eqv.add
    assumption
    assumption

instance : Neg (CauchySeq α γ) where
  neg a := {
    toFun i := -a i
    is_cauchy' := by
      apply is_cauchy_eqv.neg
      exact a.is_cauchy
  }

instance : Neg (Completion α γ) where
  neg := lift (fun a => ofSeq (-a)) <| by
    intro a b h
    apply sound
    apply is_cauchy_eqv.neg
    assumption

instance : Sub (CauchySeq α γ) where
  sub a b := (a + -b).copy (fun i => a i - b i) <| by
    intro i; symm; apply sub_eq_add_neg

instance : IsLawfulSub (CauchySeq α γ) where
  sub_eq_add_neg _ _  := copy_eq _ _ _

instance : Sub (Completion α γ) where
  sub := lift₂ (fun a b => ofSeq (a - b)) <| by
    intro a b c d ac bd
    dsimp; rw [sub_eq_add_neg, sub_eq_add_neg]
    apply sound
    apply is_cauchy_eqv.add
    assumption
    apply is_cauchy_eqv.neg
    assumption

instance : Zero (CauchySeq α γ) where
  zero := const 0
instance : Zero (Completion α γ) where
  zero := ofSeq 0

instance : One (CauchySeq α γ) where
  one := const 1
instance : One (Completion α γ) where
  one := ofSeq 1

instance : Norm (CauchySeq α γ) (CauchySeq γ γ) where
  norm c := {
    toFun i := ‖c i‖
    is_cauchy' := by
      apply is_cauchy_eqv.norm
      exact c.is_cauchy
  }

instance : Norm (Completion α γ) (Completion γ γ) where
  norm := lift (ofSeq ∘ (‖·‖)) <| by
    intro a b h; apply sound
    apply is_cauchy_eqv.norm
    assumption

variable [IsLawfulMulNorm α γ]

instance : Mul (CauchySeq α γ) where
  mul a b := {
    toFun i := a i * b i
    is_cauchy' := by
      apply is_cauchy_eqv.mul <;> rfl
  }

instance : Mul (Completion α γ) where
  mul := lift₂ (fun a b => ofSeq (a * b)) <| by
    intro a b c d ac bd
    apply sound; apply is_cauchy_eqv.mul
    assumption
    assumption

def is_cauchy_eqv.npow (a b: CauchySeq α γ) (n: ℕ) (h: a ≈ b) : is_cauchy_eqv (fun i => a i ^ n) (fun i => b i ^ n) := by
  induction n generalizing a b with
  | zero => simp [npow_zero]; apply (CauchySeq.is_cauchy 1)
  | succ n ih =>
    simp [npow_succ]
    let an : CauchySeq α γ := {
      toFun i := a i ^ n
      is_cauchy' := ih _ _ (Relation.refl _)
    }
    let bn : CauchySeq α γ := {
      toFun i := b i ^ n
      is_cauchy' := ih _ _ (Relation.refl _)
    }
    apply is_cauchy_eqv.mul an a bn b
    apply ih
    assumption
    assumption

instance : Pow (CauchySeq α γ) ℕ where
  pow a n := {
    toFun i := a i ^ n
    is_cauchy' := by apply is_cauchy_eqv.npow <;> rfl
  }

instance : Pow (Completion α γ) ℕ where
  pow := flip fun n => lift (fun a => ofSeq (a ^ n)) <| by
    intro a b ab
    apply sound; apply is_cauchy_eqv.npow
    assumption

def is_cauchy_eqv.smul (a c: CauchySeq γ γ) (b d: CauchySeq α γ) : a ≈ c -> b ≈ d -> is_cauchy_eqv (fun i => a i • b i) (fun i => c i • d i) := by
  intro ac bd ε εpos
  have ⟨Ba, Ba_pos, hBa⟩ := a.bounded_with 0
  have ⟨Bd, Bd_pos, hBd⟩ := d.bounded_with 0
  let ε₀ := ε /? (2: ℕ) /? Bd
  let ε₁ := ε /? (2: ℕ) /? Ba
  have hε₀ : 0 < ε₀ := by
    apply pos_div?
    apply half_pos
    assumption
    assumption
  have hε₁ : 0 < ε₁ := by
    apply pos_div?
    apply half_pos
    assumption
    assumption

  have ⟨k, hk⟩ := (ac _ hε₀).merge₂ (bd _ hε₁)
  exists k; intro i j hi hj; dsimp
  replace ⟨ac, bd⟩ := hk i j hi hj; clear hk
  rw [←add_zero (_ • _), ←neg_add_cancel (a i • d j),
    ←add_assoc, ←sub_eq_add_neg, add_sub_assoc,
    ←smul_sub, ←sub_smul]
  apply lt_of_le_of_lt
  apply norm_add_le_add_norm
  rw [norm_smul, norm_smul, ←half_add_half ε]
  apply add_lt_add
  · apply lt_of_le_of_lt
    apply mul_le_mul_of_nonneg_right
    apply le_of_lt; apply hBa
    apply norm_nonneg
    apply lt_of_mul_lt_mul_of_pos_left
    exact pos_inv? _ Ba_pos
    rwa [←mul_assoc, inv?_mul_cancel, one_mul, mul_comm, ←div?_eq_mul_inv?]
  · apply lt_of_le_of_lt
    apply mul_le_mul_of_nonneg_left
    apply le_of_lt; apply hBd
    apply norm_nonneg
    apply lt_of_mul_lt_mul_of_pos_right
    exact pos_inv? _ Bd_pos
    rwa [mul_assoc, mul_inv?_cancel, mul_one, ←div?_eq_mul_inv?]

instance : SMul (CauchySeq γ γ) (CauchySeq α γ) where
  smul a b := {
    toFun i := a i • b i
    is_cauchy' := by apply is_cauchy_eqv.smul <;> rfl
  }

instance Completion.instSmul : SMul (Completion γ γ) (Completion α γ) where
  smul := lift₂ (fun a b => ofSeq (a • b)) <| by
    intro a b c d ac bd; apply sound
    apply is_cauchy_eqv.smul
    assumption
    assumption

instance
  [SMul R α] [SMul R γ]
  [IsScalarTower R γ α]
  : SMul R (Completion α γ) where
  smul r a := (Completion.const (r • (1 : γ))) • a

@[simp] def const_zero : const (0: α) = (0: CauchySeq α γ) := rfl
@[simp] def Completion.const_zero : const (0: α) = (0: Completion α γ) := rfl

@[simp] def const_one : const (1: α) = (1: CauchySeq α γ) := rfl
@[simp] def Completion.const_one : const (1: α) = (1: Completion α γ) := rfl

instance : NatCast (Completion α γ) where
  natCast a := Completion.const a
instance : IntCast (Completion α γ) where
  intCast a := Completion.const a

instance : IsComm (Completion α γ) where
  mul_comm a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply mul_comm

instance : IsAddComm (Completion α γ) where
  add_comm a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply add_comm

instance : IsAddMonoid (Completion α γ) where
  add_assoc a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply add_assoc
  add_zero a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply add_zero
  zero_add a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply zero_add
  zero_nsmul a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [zero_nsmul]
    apply zero_smul
  succ_nsmul n a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [succ_nsmul, add_smul, zero_smul, zero_add]
    rw [←natCast_eq_nsmul_one]
    show (n + 1 : γ) • a i = _
    rw [add_smul, one_smul]; rfl

instance : IsMonoid (Completion α γ) where
  mul_assoc a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply mul_assoc
  mul_one a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply mul_one
  one_mul a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply one_mul
  npow_zero a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply npow_zero
  npow_succ a n := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply npow_succ

instance : IsLeftDistrib (Completion α γ) where
  mul_add a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply mul_add

instance : IsAddGroup (Completion α γ) where
  sub_eq_add_neg a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply sub_eq_add_neg
  add_neg_cancel a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply add_neg_cancel
  ofNat_zsmul a n := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [ofNat_zsmul]
  negSucc_zsmul a n := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [negSucc_zsmul]
    show (-((n + 1: ℕ) • (1: γ))) • a i = -(((n + 1: ℕ) • (1: γ)) • a i)
    rw [←neg_smul_left]

instance : IsLawfulZeroMul (Completion α γ) where
  zero_mul a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply zero_mul
  mul_zero a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply mul_zero

instance : RingOps (Completion α γ) where

instance : IsRing (Completion α γ) where
  natCast_zero := by
    show Completion.const _ = Completion.const _
    rw [natCast_zero]
  natCast_one := by
    show Completion.const _ = Completion.const _
    rw [natCast_one]
  natCast_succ n := by
    show Completion.const _ = Completion.const _ + 1
    rw [natCast_succ]; rfl
  intCast_ofNat n := by
    show Completion.const _ = Completion.const _
    rw [intCast_ofNat]
  intCast_negSucc n := by
    show Completion.const (Int.negSucc n: α) = -(Completion.const (_))
    rw [intCast_negSucc]; rfl

def constHom : α →+* CauchySeq.Completion α γ where
  toFun := CauchySeq.Completion.const
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

@[simp] def apply_constHom (a: α) : constHom a = CauchySeq.Completion.const a := rfl

variable [LE α] [LT α] [IsPartialOrder α]

def IsPos (c: CauchySeq γ γ) : Prop :=
  ∃B, 0 < B ∧ Eventually fun i => B < c i

def IsNonneg' (c: ℕ -> γ) : Prop :=
  ∃c': CauchySeq γ γ, is_cauchy_eqv c c' ∧ Eventually fun i => 0 ≤ c' i

def IsNonneg (c: CauchySeq γ γ) : Prop := IsNonneg' c

private def is_cauchy_eqv.IsPos' (a b: CauchySeq γ γ) (h: a ≈ b) : a.IsPos -> b.IsPos := by
  intro ⟨B, Bpos, hB⟩
  have ⟨k, hk⟩ := (h _ (half_pos (norm_pos.mpr (ne_of_gt Bpos)))).merge hB
  refine ⟨_, half_pos Bpos, ?_⟩
  exists k; intro i hi
  dsimp at hk
  replace ⟨hk, hBa⟩ := hk i i hi hi
  -- B ≤ B - B /? 2 < a i - ‖a i - b i‖ ≤ b i
  rw [show B /? (2: ℕ) = B - B /? (2: ℕ) from ?_]
  apply lt_of_lt_of_le
  apply sub_lt_sub
  assumption
  rw [show B = ‖B‖ from ?_]
  assumption
  rw [abs_eq_max, max_eq_left]
  apply neg_le_of_nonneg
  apply le_of_lt; assumption
  apply sub_le_iff_le_add.mpr
  rw [add_comm]
  apply le_add_iff_sub_le.mpr
  rw [abs_eq_max]
  apply left_le_max
  rw (occs := [2]) [←half_add_half B]
  rw [add_sub_assoc, sub_self, add_zero]

protected def is_cauchy_eqv.IsPos (a b: CauchySeq γ γ) (h: a ≈ b) : a.IsPos ↔ b.IsPos := by
  apply Iff.intro
  apply is_cauchy_eqv.IsPos'
  assumption
  apply is_cauchy_eqv.IsPos'
  apply Relation.symm; assumption

private def is_cauchy_eqv.IsNonneg' (a b: CauchySeq γ γ) (h: a ≈ b) : a.IsNonneg -> b.IsNonneg := by
  intro ⟨x, ha, hx⟩
  refine ⟨x, ?_, hx⟩
  show _ ≈ x
  apply Relation.trans
  apply Relation.symm
  assumption
  assumption

protected def is_cauchy_eqv.IsNonneg (a b: CauchySeq γ γ) (h: a ≈ b) : a.IsNonneg ↔ b.IsNonneg := by
  apply Iff.intro
  apply is_cauchy_eqv.IsNonneg'
  assumption
  apply is_cauchy_eqv.IsNonneg'
  apply Relation.symm; assumption

protected def Completion.IsPos : Completion γ γ -> Prop := lift IsPos (fun _ _ h => propext (is_cauchy_eqv.IsPos _ _ h))

protected def Completion.IsNonneg : Completion γ γ -> Prop := lift IsNonneg (fun _ _ h => propext (is_cauchy_eqv.IsNonneg _ _ h))

def ne_zero_of_pos (c: CauchySeq γ γ) : c.IsPos -> ¬c ≈ 0 := by
  intro pos h
  replace pos := is_cauchy_eqv.IsPos' _ _ h pos; clear h c
  obtain ⟨B, Bpos, k, h⟩ := pos
  exact Relation.asymm Bpos (h k (Nat.le_refl _))

protected def Completion.ne_zero_of_pos (c: Completion γ γ) : c.IsPos -> c ≠ 0 := by
  intro pos rfl
  apply ne_zero_of_pos _ pos
  rfl

def of_eventually_pointwise (a b: CauchySeq α γ) (h: Eventually fun i => a i = b i) : a ≈ b := by
  intro ε εpos
  replace ⟨k, h⟩ := (b.is_cauchy _ εpos).merge h
  exists k; intro i j hi hj
  replace ⟨ha, h⟩ := h i j hi hj
  rwa [h]

def Completion.of_eventually_pointwise (a b: CauchySeq α γ) (h: Eventually fun i => a i = b i) : ofSeq a = ofSeq b := by
  apply sound
  apply CauchySeq.of_eventually_pointwise
  assumption

instance : IsZeroNeOne (CauchySeq.Completion α γ) where
  zero_ne_one := by
    intro h
    have one_pos : CauchySeq.Completion.IsPos (‖(1: CauchySeq.Completion α γ)‖) := by
      exists 1 /? (2: ℕ)
      apply And.intro
      apply pos_div?_natCast
      apply zero_lt_one
      exists 0; intro i hi
      dsimp; show (1 /? (2: ℕ)~(_): γ) < ‖(1: α)‖
      apply lt_of_mul_lt_mul_of_pos_right _ _ ((2: ℕ): γ)
      apply pos_natCast; rw [div?_mul_cancel, norm_one, one_mul]
      rw [←natCast_one]; apply (natCast_lt_natCast _ _).mpr
      decide
    have zero_not_pos : ¬CauchySeq.Completion.IsPos (‖(0: CauchySeq.Completion α γ)‖) := by
      intro h
      have : ¬(‖(0: CauchySeq α γ)‖ ≈ 0) := ne_zero_of_pos _ h
      apply this
      apply of_eventually_pointwise
      exists 0; intro i hi
      apply norm_zero
    rw [h] at zero_not_pos
    contradiction

def norm_pos_of_ne_zero [LEM] (c: CauchySeq α γ) (h: ¬c ≈ 0) : ‖c‖.IsPos := by
  apply LEM.byContradiction; intro g
  replace g := not_exists.mp g
  simp only [Eventually, not_and, not_exists, LEM.not_forall, not_lt] at g
  replace g : ∀ε: γ, 0 < ε -> ∀i, ∃(j: ℕ) (h: i ≤ j), ‖c j‖ ≤ ε := g
  apply h; clear h
  intro ε εpos
  have := g _ (half_pos εpos)
  have ⟨k, hk⟩ := c.is_cauchy _ (half_pos εpos)
  exists k; intro i j hi hj
  show ‖c i - 0‖ < ε; rw [sub_zero]
  clear hj j
  have ⟨j, i_le_j, hj⟩ := this i
  rw [←add_zero (c i), ←neg_add_cancel (c j)]
  rw [←add_assoc, ←sub_eq_add_neg, ←half_add_half ε]
  apply lt_of_le_of_lt
  apply norm_add_le_add_norm
  apply lt_of_le_of_lt
  apply add_le_add_left
  assumption
  apply add_lt_add_right
  apply hk
  assumption
  apply le_trans
  assumption
  assumption

def norm_ne_zero (a: α) (ha: a ≠ 0) : ‖a‖ ≠ 0 := by
  intro h; apply ha
  apply of_norm_eq_zero
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply norm_ne_zero <;> invert_tactic)

private def norm_inv? (a: α) (ha: a ≠ 0) : ‖a⁻¹?‖ = ‖a‖⁻¹? := by
  apply eq_inv?_of_mul
  rw [←norm_mul, inv?_mul_cancel, norm_one]

instance : IsLinearOrder γ := inferInstance
instance : @Relation.IsIrrefl γ (· < ·) := inferInstance
instance : @Relation.IsAsymm γ (· < ·) := inferInstance

protected def is_cauchy_eqv.safe_inv
  [IsLawfulMulNorm α γ] [DecidableEq α] [LEM]
  {a b: CauchySeq α γ}
  (h: a ≈ b) (ha: ¬a ≈ 0) :
  is_cauchy_eqv (safe_inv a) (safe_inv b) := by
  have hb: ¬b ≈ 0 := by intro hb; exact ha (Relation.trans h hb)
  have ⟨Ba, Ba_pos, hBa⟩ := norm_pos_of_ne_zero _ ha
  have ⟨Bb, Bb_pos, hBb⟩ := norm_pos_of_ne_zero _ hb
  have hB := hBa.merge hBb; clear hBa hBb
  intro ε εpos
  replace h := (h _ (pos_mul_of_pos _ _ εpos (pos_mul_of_pos _ _ Ba_pos Bb_pos))).merge hB; clear hB
  obtain ⟨k, hk⟩ := h
  exists k
  intro i j hi hj
  simp [safe_inv]
  replace ⟨y, x, hBb⟩ := hk j i hj hi; clear x y
  replace ⟨hk, hBa, hBb'⟩ := hk i j hi hj; clear hBb'
  replace hBa : Ba < ‖a i‖ := hBa
  replace hBb : Bb < ‖b j‖ := hBb
  have := pos_mul_of_pos _ _ (lt_trans Ba_pos hBa) (lt_trans Bb_pos hBb)
  rw [dif_neg, dif_neg]
  · rw [←one_div?, ←one_div?, div?_sub_div?, one_mul, one_mul]
    rw [div?_eq_mul_inv?, norm_mul, norm_inv?, norm_sub]
    apply lt_of_lt_of_le
    apply mul_lt_mul_of_pos_right
    assumption
    apply pos_inv?
    apply not_le.mp
    intro g
    replace g := le_antisymm g (norm_nonneg _)
    rw [norm_mul] at g
    rw [g] at this
    exact Relation.irrefl this
    rw (occs := [2]) [←mul_one ε]; rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left
    apply le_of_lt
    apply lt_of_mul_lt_mul_of_pos_right
    show 0 < ‖a i * b j‖
    rw [norm_mul]; assumption
    rw [mul_assoc, inv?_mul_cancel, one_mul, norm_mul, mul_one]
    apply lt_trans
    apply mul_lt_mul_of_pos_left
    assumption
    assumption
    apply mul_lt_mul_of_pos_right
    assumption
    apply flip lt_trans
    assumption
    assumption
    apply le_of_lt
    assumption
  · intro h; rw [h, norm_zero] at hBb
    exact Relation.asymm hBb Bb_pos
  · intro h; rw [h, norm_zero] at hBa
    exact Relation.asymm hBa Ba_pos

instance [DecidableEq α] [LEM] : CheckedInv (CauchySeq α γ) (fun a => ¬a ≈ 0) where
  checked_inv a h := {
    toFun := safe_inv a
    is_cauchy' := by
      apply is_cauchy_eqv.safe_inv
      rfl
      assumption
  }

def lift_with {P: Completion α γ -> Prop} (f: ∀c, P (ofSeq c) -> β) (hf: ∀(a b: CauchySeq α γ) (h: a ≈ b) (pa: P (ofSeq a)), f a pa = f b (sound h ▸ pa)) (a: Completion α γ) (pa: P a) : β :=
  (a.toQuot.hrecOn (motive := fun c: Quotient (setoid (α := α) (γ := γ)) => P (.ofQuot c) -> β) f · pa) <| by
    intro a b h
    apply Function.hfunext
    have := hf a b h
    rw [sound h]
    intro ha hb h_
    simp; apply hf
    assumption

instance [DecidableEq α] [LEM] : CheckedInv? (Completion α γ) where
  checked_inv := lift_with (P := (· ≠ 0)) (fun c hc =>
    have : ¬c ≈ 0 := fun g => hc (sound g)
    ofSeq c⁻¹?) <| by
    intro a b h pa
    dsimp
    apply sound
    apply is_cauchy_eqv.safe_inv
    assumption
    intro g; exact pa (sound g)


def of_norm_pos (c: CauchySeq γ γ) : ‖c‖.IsPos -> c.IsPos ∨ (-c).IsPos := by
  intro ⟨B, Bpos, hB⟩
  replace hB := (c.is_cauchy _ (half_pos Bpos)).merge hB
  replace ⟨k, hB⟩ := hB
  dsimp at hB
  -- have := hB k k (Nat.le_refl _) (Nat.le_refl _)
  have : B < ‖c k‖ := (hB k k (Nat.le_refl _) (Nat.le_refl _)).right
  rw [abs_eq_max] at this
  rcases of_lt_max this with h | h
  · left; refine ⟨_, Bpos, k, fun i hi => ?_⟩
    dsimp
    replace ⟨hc, hB⟩ := hB i k hi (Nat.le_refl _)
    replace hB : B < ‖c i‖ := hB
    rw [abs_eq_max] at hB
    rcases of_lt_max hB with hB | hB
    assumption
    rw [←neg_lt_neg_iff, neg_neg] at hB
    have := sub_lt_sub h hB
    rw [sub_eq_add_neg, neg_neg] at this
    rw [norm_sub, abs_eq_max] at hc
    have := lt_trans this (lt_of_le_of_lt left_le_max hc)
    rw [←zero_add (B /? (2: ℕ)), lt_add_iff_sub_lt, add_sub_assoc] at this
    rw [show (B - B /? (2: ℕ)) = B /? (2: ℕ) by
      rw (occs := [1]) [←half_add_half B]
      rw [add_sub_assoc, sub_self, add_zero]] at this
    have := lt_of_le_of_lt (by
      show B ≤ B + B /? (2: ℕ)
      apply le_add_right
      apply le_of_lt
      apply pos_div?_natCast
      assumption) this
    nomatch Relation.asymm Bpos this
  · right; refine ⟨_, Bpos, k, fun i hi => ?_⟩
    dsimp
    replace ⟨hc, hB⟩ := hB i k hi (Nat.le_refl _)
    replace hB : B < ‖c i‖ := hB
    rw [abs_eq_max] at hB
    rcases Or.symm (of_lt_max hB) with hB | hB
    assumption
    -- rw [←neg_lt_neg_iff, neg_neg] at hB
    have := sub_lt_sub hB h
    rw [sub_eq_add_neg, neg_neg, lt_sub_iff_add_lt,
      add_assoc, add_comm (c k), ←add_assoc,
      add_lt_iff_lt_sub] at this
    rw [abs_eq_max] at hc
    have := lt_trans this (lt_of_le_of_lt left_le_max hc)
    rw [←zero_add (B /? (2: ℕ)), lt_add_iff_sub_lt, add_sub_assoc] at this
    rw [show (B - B /? (2: ℕ)) = B /? (2: ℕ) by
      rw (occs := [1]) [←half_add_half B]
      rw [add_sub_assoc, sub_self, add_zero]] at this
    have := lt_of_le_of_lt (by
      show B ≤ B + B /? (2: ℕ)
      apply le_add_right
      apply le_of_lt
      apply pos_div?_natCast
      assumption) this
    nomatch Relation.asymm Bpos this

protected def Completion.of_norm_pos (c: Completion γ γ) : ‖c‖.IsPos -> c.IsPos ∨ (-c).IsPos := by
  induction c with | _ c =>
  apply of_norm_pos

protected def Completion.norm_pos_of_ne_zero [LEM] (c: Completion α γ) (h: c ≠ 0) : ‖c‖.IsPos := by
  induction c with | _ c =>
  apply norm_pos_of_ne_zero
  intro g; apply h; apply sound
  assumption

instance : LE (Completion γ γ) where
  le a b := (b - a).IsNonneg
instance : LT (Completion γ γ) where
  lt a b := a ≤ b ∧ ¬b ≤ a

def nonneg_of_pos (c: CauchySeq γ γ) : c.IsPos -> c.IsNonneg := by
  intro ⟨B, Bpos, k, hk⟩
  refine ⟨c, c.is_cauchy, k, ?_⟩
  intro i hi
  apply le_of_lt; apply lt_trans Bpos
  apply hk; assumption

def nonneg_of_zero : IsNonneg (.const (0: γ)) := by
  refine ⟨_, CauchySeq.is_cauchy _, 0, ?_⟩
  intro i hi
  apply le_refl

def not_nonneg_of_neg (c: CauchySeq γ γ) : (-c).IsPos -> ¬c.IsNonneg := by
  intro neg ⟨x, hc, hx⟩
  have : -c ≈ -x := is_cauchy_eqv.neg hc
  have ⟨B, Bpos, evenneg⟩ := is_cauchy_eqv.IsPos' _ _ this neg
  replace even := hx.merge evenneg; clear evenneg this hc neg c hx
  obtain ⟨k, hk⟩ := even
  replace ⟨nonneg, neg⟩ := hk k (le_refl _)
  apply not_le_of_lt (lt_trans Bpos neg)
  show -x k ≤ 0
  rw [←neg_zero]; apply neg_le_neg
  assumption

protected def nonneg_add (a b: CauchySeq γ γ) : a.IsNonneg -> b.IsNonneg -> (a + b).IsNonneg := by
  intro ⟨x, ha, hx⟩ ⟨y, hb, hy⟩
  exists x + y
  apply And.intro
  apply is_cauchy_eqv.add
  assumption
  assumption
  have ⟨k, hk⟩ := hx.merge hy; clear hx hy
  exists k; intro i hi
  apply nonneg_add
  exact (hk i hi).left
  exact (hk i hi).right

def eqv_zero_of_nonneg_and_nonpos' (a: ℕ -> γ) : IsNonneg' a -> IsNonneg' (fun i => -a i) -> is_cauchy_eqv a (fun _ => 0) := by
  intro ⟨x, hpa, hx⟩ ⟨u, hna, hu⟩
  have : is_cauchy_eqv (fun i => a i + -a i) (x + u) := is_cauchy_eqv.add hpa hna
  replace := symm this
  rw [show (fun i => a i + -a i) = (fun i => 0) by ext; apply add_neg_cancel] at this
  apply trans x.is_cauchy hpa
  intro ε εpos
  have ⟨k, hk⟩ := (this ε εpos).merge (hx.merge hu)
  exists k; intro i j hi hj
  have ⟨hxu, hx, hu⟩ := hk i j hi hj
  show ‖x i - 0‖ < ε; rw [sub_zero]
  replace hxu : ‖(x i + u i) - 0‖ < ε := hxu
  rw [sub_zero] at hxu
  apply lt_of_le_of_lt _ hxu
  rw [abs_eq_of_nonneg, abs_eq_of_nonneg]
  apply le_add_right
  assumption
  apply nonneg_add
  assumption
  assumption
  assumption

def eqv_of_antisymm' (a: ℕ -> γ) (b: CauchySeq γ γ) : IsNonneg' (fun i => a i - b i) -> IsNonneg' (fun i => b i - a i) -> is_cauchy_eqv a b := by
  intro h g
  conv at g => { rhs; intro i; rw [←neg_sub] }
  have := eqv_zero_of_nonneg_and_nonpos' _ h g
  have := is_cauchy_eqv.add this b.is_cauchy
  simpa [zero_add, sub_add_assoc, neg_add_cancel, add_zero] using this

def eqv_zero_of_nonneg_and_nonpos (a: CauchySeq γ γ) : a.IsNonneg -> (-a).IsNonneg -> a ≈ 0 := by
  apply eqv_zero_of_nonneg_and_nonpos'

def not_pos_and_neg (c: CauchySeq γ γ) : c.IsPos -> (-c).IsPos -> False := by
  intro ⟨A, Apos, hA⟩ ⟨B, Bpos, hB⟩
  have ⟨k, hk⟩ := hA.merge hB
  have ⟨ha, hb⟩ := hk k (Nat.le_refl k)
  replace hb : B < - c k := hb
  rw [←neg_lt_neg_iff, neg_neg] at hb
  apply Relation.asymm Apos
  apply lt_trans (lt_trans ha hb)
  rwa [←neg_lt_neg_iff, neg_zero, neg_neg]

protected def pos_add (a b: CauchySeq γ γ) : a.IsPos -> b.IsPos -> (a + b).IsPos := by
  intro ⟨A, Apos, hA⟩
  intro ⟨B, Bpos, hB⟩
  have ⟨k, hk⟩ := hA.merge hB
  refine ⟨A + B, ?_, ?_⟩
  apply pos_add
  assumption
  assumption
  exists k; intro i hi
  replace hk := hk i hi
  apply add_lt_add
  exact hk.left
  exact hk.right

protected def Completion.not_pos_and_neg (c: Completion γ γ) : c.IsPos -> (-c).IsPos -> False := by
  induction c
  apply not_pos_and_neg

protected def Completion.pos_add (a b: Completion γ γ) : a.IsPos -> b.IsPos -> (a + b).IsPos := by
  induction a
  induction b
  apply CauchySeq.pos_add

instance [LEM] : Relation.IsConnected (α := Completion γ γ) (fun a b => (b - a).IsPos) (· = ·) where
  connected a b := by
    rcases em (a = b) with h | h
    right; left; assumption
    rw [sub_eq_zero] at h
    replace this := Completion.norm_pos_of_ne_zero _ h
    rcases Completion.of_norm_pos _ this with h | h
    right; right; assumption
    left;  rwa [neg_sub] at h

-- instance : @Relation.IsTrans (Completion γ γ) (· < ·) where
--   trans {a b c} h g := by
--     show Completion.IsPos _
--     replace h : Completion.IsPos _ := h
--     replace g : Completion.IsPos _ := g
--     rw [←add_zero c, ←neg_add_cancel b, ←add_assoc, ←sub_eq_add_neg, add_sub_assoc]
--     apply Completion.pos_add <;> assumption
-- instance : @Relation.IsIrrefl (Completion γ γ) (· < ·) where
--   irrefl {a} h := by
--     replace h : Completion.IsPos (a - a) := h
--     rw [sub_self] at h
--     exact Completion.ne_zero_of_pos _ h rfl
-- instance : @Relation.IsAsymm (Completion γ γ) (· < ·) := inferInstance

instance : Relation.IsAntisymm (α := Completion γ γ) (· ≤ ·) (· = ·) where
  antisymm {a b} h g := by
    replace h : Completion.IsNonneg _ := h
    replace g : Completion.IsNonneg _ := g
    rw [←neg_sub] at g
    cases a using ind with | _ a =>
    cases b using ind with | _ b =>
    have := eqv_zero_of_nonneg_and_nonpos _ h g
    have : ofSeq b - ofSeq a = 0 := (sound this)
    symm; exact (sub_eq_zero _ _).mpr this

instance : IsPartialOrder (Completion γ γ) where
  lt_iff_le_and_not_ge {a b} := Iff.rfl
  refl _ := by
    show Completion.IsNonneg _
    rw [sub_self]; apply nonneg_of_zero
  trans {a b c} := by
    show Completion.IsNonneg _ -> Completion.IsNonneg _ -> Completion.IsNonneg _
    intro h g
    rw [←add_zero c, ←neg_add_cancel b, ←add_assoc,
      ←sub_eq_add_neg, add_sub_assoc]
    cases a using ind with | _ a =>
    cases b using ind with | _ b =>
    cases c using ind with | _ c =>
    apply CauchySeq.nonneg_add
    assumption
    assumption

instance [LEM] : Relation.IsTotal (α := Completion γ γ) (· ≤ ·) where
  total a b := by
    rcases Relation.connected (fun a b => (b - a).IsPos) a b with h | h | h
    · left
      cases a using ind with | _ a =>
      cases b using ind with | _ b =>
      apply nonneg_of_pos
      assumption
    · left; rw [h]
    · right
      cases a using ind with | _ a =>
      cases b using ind with | _ b =>
      apply nonneg_of_pos
      assumption

instance [LEM] : IsLinearOrder (Completion γ γ) where

def le_of_eventually_le (a b: CauchySeq γ γ) : (Eventually fun i => a i ≤ b i) -> ofSeq a ≤ ofSeq b := by
  intro h
  show IsNonneg (b - a)
  exists b - a
  apply And.intro (CauchySeq.is_cauchy _)
  obtain ⟨k, hk⟩ := h
  exists k; intro i hi
  replace hk := hk i hi
  apply le_sub_iff_add_le.mpr
  rwa [zero_add]

protected def Completion.norm_add_le_add_norm (a b: Completion α γ) : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := by
  induction a with | _ a =>
  induction b with | _ b =>
  apply le_of_eventually_le
  exists 0; intro i hi
  apply norm_add_le_add_norm

protected def Completion.norm_nonneg (a: Completion α γ) : 0 ≤ ‖a‖ := by
  induction a with | _ a =>
  apply le_of_eventually_le
  exists 0; intro i hi
  apply norm_nonneg

protected def Completion.norm_smul (a: Completion γ γ) (b: Completion α γ) : ‖a • b‖ = ‖a‖ * ‖b‖  := by
  induction a with | _ a =>
  induction b with | _ b =>
  show ofSeq _ = ofSeq _; congr 1; ext i
  apply norm_smul

protected def Completion.norm_zero : ‖(0: Completion α γ)‖ = 0  := by
  show ofSeq _ = ofSeq _; congr 1; ext i
  apply norm_zero
protected def Completion.of_norm_eq_zero (a: Completion α γ) : ‖a‖ = 0 -> a = 0 := by

  induction a with | _ a =>
  intro h; replace h : ‖a‖ ≈ 0 := exact h
  apply sound
  intro ε εpos
  replace ⟨k, h⟩ := h ε εpos
  exists k; intro i j hi hj
  show ‖a i - 0‖ < _; rw [sub_zero]
  have : ‖‖a i‖ - 0‖ < ε := h i j hi hj
  rwa [sub_zero, norm_abs] at this
protected def Completion.norm_eq_zero {a: Completion α γ} : ‖a‖ = 0 ↔ a = 0 := by
  apply Iff.intro
  apply Completion.of_norm_eq_zero
  intro rfl; exact Completion.norm_zero

instance : IsLawfulAbs (Completion γ γ) where
  abs_nonneg := Completion.norm_nonneg
  abs_mul := Completion.norm_smul
  abs_add_le_add_abs := Completion.norm_add_le_add_norm
  abs_eq_zero := Completion.norm_eq_zero

instance : IsLawfulNorm (Completion α γ) (Completion γ γ) where
  norm_nonneg := Completion.norm_nonneg
  norm_smul := Completion.norm_smul
  norm_add_le_add_norm := Completion.norm_add_le_add_norm
  norm_eq_zero := Completion.norm_eq_zero

def eventually_ne_zero_of_ne_zero [LEM] (a: CauchySeq α γ) (h: ¬a ≈ 0) : Eventually fun i => a i ≠ 0 := by
  have ⟨B, Bpos, k, h⟩ := norm_pos_of_ne_zero _ h
  exists k; intro i hi; replace h : B < ‖a i‖ := h i hi
  intro  g
  rw [←norm_eq_zero] at g
  rw [g] at h
  exact Relation.asymm Bpos h

instance : IsAbsMax (Completion γ γ) where
  abs_eq_of_nonneg a ha := by
    apply flip le_antisymm
    · cases a using ind with | _ a =>
      apply le_of_eventually_le
      exists 0; intro i hi
      show a i ≤ ‖a i‖
      rw [abs_eq_max]; apply left_le_max
    · replace ha : Completion.IsNonneg (a - 0) := ha
      rw [sub_zero] at ha
      cases a using ind with | _ a =>
      obtain ⟨x, ha, hx⟩ := ha
      rw [sound ha]
      show IsNonneg _; dsimp
      exists 0; apply And.intro
      obtain ⟨k, hk⟩ := hx
      apply of_eventually_pointwise
      exists k; intro i hi
      show x i - ‖x i‖ = 0
      rw [abs_eq_of_nonneg, sub_self]
      apply hk; assumption
      exists 0; intro _ _; rfl

instance [DecidableEq α] [LEM] : CheckedDiv? (Completion α γ) where
  checked_div a b h := a * b⁻¹?
instance [DecidableEq α] [LEM] : CheckedZPow? (Completion α γ) where
  checked_pow a b h :=
    match b with
    | .ofNat b => a ^ b
    | .negSucc b => a⁻¹? ^ (b + 1)

instance [DecidableEq α] [LEM] : GroupWithZeroOps (Completion α γ) := inferInstance
instance [DecidableEq α] : AddGroupWithOneOps (Completion α γ) := inferInstance
instance (priority := 100000) [DecidableEq α] [LEM] : FieldOps (Completion α γ) := instFieldOpsOfGroupWithZeroOpsOfAddGroupWithOneOps

instance [DecidableEq α] [LEM] : IsGroupWithZero (Completion α γ) where
  zero_ne_one := by
    intro h
    replace h := exact h
    have ⟨k, hk⟩ := h ((1: γ) /? (2: ℕ)) (by
      apply pos_div?_natCast
      apply zero_lt_one)
    replace hk : ‖(0 - 1: α)‖ < (1: γ) /? (2: ℕ) := hk _ _ (Nat.le_refl _) (Nat.le_refl _)
    dsimp at hk
    rw [norm_sub, sub_zero, norm_one]  at hk
    have := mul_lt_mul_of_pos_left _ _ hk (2: ℕ) (pos_natCast _)
    rw [div?_eq_mul_inv?, one_mul, mul_inv?_cancel, mul_one, ←natCast_one,
      natCast_lt_natCast] at this
    contradiction
  div?_eq_mul_inv? _ _ _ := rfl
  zpow?_ofNat _ _ := rfl
  zpow?_negSucc _ _ _ := rfl
  mul_inv?_cancel a h := by
    induction a with | _ a =>
    have ⟨k, hk⟩ := eventually_ne_zero_of_ne_zero _ (fun g => h (sound g))
    apply sound; apply of_eventually_pointwise; exists k; intro i hi
    show a i * safe_inv a i = 1
    unfold safe_inv; rw [dif_neg]
    apply mul_inv?_cancel
    apply hk
    assumption

def is_cauchy_eqv.offset (a b: ℕ -> α) (h: is_cauchy_eqv a b) (n: ℕ) : is_cauchy_eqv (fun i => a (i + n)) (fun i => b (i + n)) := by
  intro ε εpos
  have ⟨k, hk⟩ := h ε εpos
  exists k; intros i j hi hj
  apply hk
  apply Nat.le_trans hi; apply Nat.le_add_right
  apply Nat.le_trans hj; apply Nat.le_add_right

def offset (c: CauchySeq α γ) (n: ℕ) : CauchySeq α γ where
  toFun i := c (i + n)
  is_cauchy' := by
    apply is_cauchy_eqv.offset
    apply c.is_cauchy

protected def is_cauchy_eqv.inv
  [IsLawfulMulNorm α γ] [LEM]
  {a b: CauchySeq α γ}
  (h: a ≈ b) (ha: ¬a ≈ 0) (ha': ∀i, a i ≠ 0) (hb': ∀i, b i ≠ 0) :
  is_cauchy_eqv (fun i => (a i)⁻¹?~(ha' _)) (fun i => (b i)⁻¹?~(hb' _)) := by
  have hb: ¬b ≈ 0 := by intro hb; exact ha (Relation.trans h hb)
  have ⟨Ba, Ba_pos, hBa⟩ := norm_pos_of_ne_zero _ ha
  have ⟨Bb, Bb_pos, hBb⟩ := norm_pos_of_ne_zero _ hb
  have hB := hBa.merge hBb; clear hBa hBb
  intro ε εpos
  replace h := (h _ (pos_mul_of_pos _ _ εpos (pos_mul_of_pos _ _ Ba_pos Bb_pos))).merge hB; clear hB
  obtain ⟨k, hk⟩ := h
  exists k
  intro i j hi hj
  replace ⟨y, x, hBb⟩ := hk j i hj hi; clear x y
  replace ⟨hk, hBa, hBb'⟩ := hk i j hi hj; clear hBb'
  replace hBa : Ba < ‖a i‖ := hBa
  replace hBb : Bb < ‖b j‖ := hBb
  have := pos_mul_of_pos _ _ (lt_trans Ba_pos hBa) (lt_trans Bb_pos hBb)
  show ‖(a i)⁻¹?~(_) - (b j)⁻¹?~(_)‖ < _
  · rw [←one_div?, ←one_div?, div?_sub_div?, one_mul, one_mul]
    rw [div?_eq_mul_inv?, norm_mul, norm_inv?, norm_sub]
    apply lt_of_lt_of_le
    apply mul_lt_mul_of_pos_right
    assumption
    apply pos_inv?
    apply not_le.mp
    intro g
    replace g := le_antisymm g (norm_nonneg _)
    rw [norm_mul] at g
    rw [g] at this
    exact Relation.irrefl this
    rw (occs := [2]) [←mul_one ε]; rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left
    apply le_of_lt
    apply lt_of_mul_lt_mul_of_pos_right
    show 0 < ‖a i * b j‖
    rw [norm_mul]; assumption
    rw [mul_assoc, inv?_mul_cancel, one_mul, norm_mul, mul_one]
    apply lt_trans
    apply mul_lt_mul_of_pos_left
    assumption
    assumption
    apply mul_lt_mul_of_pos_right
    assumption
    apply flip lt_trans
    assumption
    assumption
    apply le_of_lt
    assumption

@[implicit_reducible]
private def is_unit_of_ne_zero [LEM] (x: Completion α γ) (hx: x ≠ 0) : IsUnit x := by
  cases x using ind with | _ x =>
  have h := (norm_pos_of_ne_zero _ (by intro g; apply hx; exact sound g))
  obtain ⟨B, Bpos, k, hk⟩ := h
  refine ⟨{
    val := ofSeq (x.offset k)
    inv := ofSeq {
      toFun i := (x (i + k))⁻¹?~(by
        intro h
        have : B < ‖x (i + k)‖ := hk (i + k) ?_
        rw [h, norm_zero] at this
        exact Relation.asymm this Bpos
        exact Nat.le_add_left k i)
      is_cauchy' := ?_
    }
    inv_mul_val := ?_
    val_mul_inv := ?_
  }, ?_⟩
  · apply is_cauchy_eqv.inv (a := x.offset k) (b := x.offset k) (Relation.refl _)
    intro h
    apply hx
    apply sound
    apply Relation.trans _ h
    intro ε εpos
    have ⟨k, hk⟩ := x.is_cauchy ε εpos
    exists k; intro i j hi hj
    apply hk
    assumption
    apply le_trans hj; apply le_add_right; apply bot_le
  · apply sound; apply of_eventually_pointwise
    exists 0; intro i hi
    show x (i + k) * (x (i + k))⁻¹?~(_) = 1
    rw [mul_inv?_cancel]
  · apply sound; apply of_eventually_pointwise
    exists 0; intro i hi
    show (x (i + k))⁻¹?~(_) * x (i + k) = 1
    rw [inv?_mul_cancel]
  · dsimp; apply sound
    intro ε εpos
    have ⟨k, hk⟩ := x.is_cauchy ε εpos
    exists k; intro i j hi hj
    apply hk
    assumption
    apply le_trans hj; apply le_add_right; apply bot_le

instance [LEM] : IsLeftCancel₀ (Completion α γ) where
  of_mul_left₀ {k a b} hk h := by
    have ⟨k', hk'⟩ := is_unit_of_ne_zero k hk
    rw [hk'] at h; clear k hk' hk
    rw [←one_mul a, ←one_mul b, ←k'.inv_mul_val,
      mul_assoc, mul_assoc, h]

instance [LEM] : NoZeroDivisors (Completion α γ) := inferInstance
instance (priority := 100000) [DecidableEq α] [LEM] : IsField (Completion α γ) where

instance : IsZeroLEOne (Completion γ γ) where
  zero_le_one := by
    show (1 - 0: CauchySeq.Completion γ γ).IsNonneg
    rw [sub_zero]
    exists 1; apply And.intro (CauchySeq.is_cauchy _)
    exists 0; intro i hi
    apply zero_le_one

private def nonneg_iff {a: Completion γ γ} : 0 ≤ a ↔ a.IsNonneg := by
  show (a - 0).IsNonneg ↔ _
  rw [sub_zero]

protected def mul_nonneg {a b: CauchySeq γ γ} (ha: IsNonneg a) (hb: IsNonneg b) : IsNonneg (a * b) := by
  obtain ⟨x, ha', hx⟩ := ha
  obtain ⟨y, ha', hy⟩ := hb
  exists x * y; apply And.intro
  · apply is_cauchy_eqv.mul
    assumption
    assumption
  have ⟨k, hk⟩ := hx.merge hy
  exists k; intro i hi
  apply mul_nonneg
  apply (hk _ hi).left
  apply (hk _ hi).right

protected def Completion.mul_nonneg {a b: Completion γ γ} (ha: 0 ≤ a) (hb: 0 ≤ b) : 0 ≤ a * b := by
  cases a using ind with | _ a =>
  cases b using ind with | _ b =>
  rw [nonneg_iff] at *
  apply CauchySeq.mul_nonneg
  assumption
  assumption

protected def Completion.lt_of_pos [LEM] {a b: Completion γ γ} (ha: Completion.IsPos (b - a)) : a < b := by
  cases a using ind with | _ a =>
  cases b using ind with | _ b =>
  rw [←not_le]; intro ⟨s, s_eqv, hs⟩
  replace s_eqv : -(a - b) ≈ (-s) := is_cauchy_eqv.neg s_eqv
  rw [←neg_sub] at ha
  replace ha : Completion.IsPos (ofSeq (-(a - b))) := ha
  rw [sound s_eqv] at ha
  clear s_eqv a b
  obtain ⟨B, Bpos, hs'⟩ := ha
  replace hs := hs.merge hs'
  obtain ⟨k, hs⟩ := hs
  replace ⟨hs, hs'⟩ := hs k (le_refl _)
  rw [←neg_le_neg_iff, neg_zero] at hs
  replace hs := lt_of_lt_of_le hs' hs
  exact Relation.asymm hs Bpos

protected def Completion.mul_le_mul_of_nonneg_left {a b: Completion γ γ} : a ≤ b → ∀ (c : Completion γ γ), 0 ≤ c → c * a ≤ c * b := by
  intro h c hc
  show Completion.IsNonneg _
  rw [←mul_sub]; rw [nonneg_iff] at hc
  replace h : (b - a).IsNonneg := h
  cases a using ind
  cases b using ind
  cases c using ind
  apply CauchySeq.mul_nonneg
  assumption
  assumption

instance : IsOrderedSemiring (Completion γ γ) where
  add_le_add_left {a b} h c := by
    show Completion.IsNonneg _
    rwa [add_comm c a, sub_add,  add_comm c,
      add_sub_assoc, sub_self, add_zero]
  mul_nonneg {a b} ha hb := by
    apply Completion.mul_nonneg
    assumption
    assumption
  mul_le_mul_of_nonneg_left := Completion.mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right {a b} h c hc := by
    rw [mul_comm _ c, mul_comm _ c]
    apply Completion.mul_le_mul_of_nonneg_left <;> assumption

protected def Completion.mul_pos [LEM] {a b: Completion γ γ} (ha: 0 < a) (hb: 0 < b) : 0 < a * b := by
  obtain ⟨ha, nha⟩ := ha
  obtain ⟨hb, nhb⟩ := hb
  apply And.intro
  · apply Completion.mul_nonneg
    assumption
    assumption
  · intro h
    have := le_antisymm h (mul_nonneg ha hb)
    rcases of_mul_eq_zero this with g | g
    apply nha; rw [g]
    apply nhb; rw [g]

instance [LEM] : IsStrictOrderedSemiring (Completion γ γ) where
  mul_pos {a b} ha hb := by
    apply Completion.mul_pos
    assumption
    assumption

instance
  [SMul R α] [SMul R γ] [IsScalarTower R γ α]
  [SemiringOps R] [IsSemiring R]
  [IsModule R γ] [IsModule γ α]
  : IsModule R (Completion α γ) where
  one_smul a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [one_smul]
    apply one_smul
  mul_smul r s a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [mul_smul]
    show (r • s • (1: γ)) • a i = (r • (1: γ)) • ((s • (1: γ)) • a i)
    rw [smul_assoc, smul_assoc, one_smul, smul_assoc r, one_smul]
  smul_zero r := by
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply smul_zero
  smul_add r a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    apply smul_add
  add_smul r s a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [add_smul];
    apply add_smul
  zero_smul a :=  by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    simp [zero_smul]; apply zero_smul

end CauchySeq

namespace CauchySeq

variable
  [CauchySeq.MetricFieldOps γ] [CauchySeq.IsMetricField γ]
  [FieldOps α] [IsField α] [FieldOps β] [IsField β]
  [CauchySeq.VectorSpaceOps α γ] [CauchySeq.VectorSpaceOps β γ]
  [CauchySeq.IsVectorSpace α γ] [CauchySeq.IsVectorSpace β γ]
  [SMul α γ] [IsScalarTower α γ α]
  [IsLawfulNorm α γ] [IsLawfulMulNorm α γ]

instance : AlgebraMap α (Completion α γ) where
  toAlgebraMap := {
    toFun := CauchySeq.Completion.const
    map_zero := rfl
    map_one := rfl
    map_add _ _ := rfl
    map_mul _ _ := rfl
  }

instance : IsAlgebra α (Completion α γ) where
  commutes _ _ := by rw [mul_comm]
  smul_def r a := by
    induction a with | _ a =>
    show ofSeq _ = ofSeq _; congr 1; ext i
    show (r • (1: γ)) • a i = _
    rw [smul_assoc, one_smul, smul_def]
    rfl

end CauchySeq

end
