import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Ring.Order
import LeanMath.Algebra.Semifield.Order
import LeanMath.Algebra.Norm.Basic
import LeanMath.Data.Fintype.Order
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

variable {α γ: Type*} [Norm α γ] [LE γ] [LT γ] [IsLinearOrder γ]
  [FieldOps α] [IsField α]
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

variable
  [Norm γ γ] [SMul γ α]
  [IsLawfulAbs γ] [IsLawfulNorm α γ]
  [IsStrictOrderedSemiring γ] [IsZeroNeOne γ]
  [IsDistributiveAction γ α]
  [IsLeftDistribSMul γ α]
  [IsLawfulZeroSMul γ α]
  [IsZeroLEOne γ]
  [Max γ] [IsSemiLatticeMax γ] [IsAbsMax γ]

local macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply natCast_ne_zero)

private def half_pos {a: γ} (h: 0 < a) : 0 < a /? (2: ℕ) := pos_div?_natCast h 1

variable [DecidableEq α]

def safe_inv (a: ℕ -> α) (i: ℕ): α :=
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
  {a b c d: CauchySeq α γ}
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

structure Completion (α γ: Type*)
  [Norm α γ] [LE γ] [LT γ] [IsLinearOrder γ]
  [FieldOps α] [IsField α]
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

@[ext] def ext (a b: CauchySeq α γ) (h: ∀i, a i = b i) : a = b := DFunLike.ext a b h
def copy (c: CauchySeq α γ) (f: ℕ -> α) (hf: ∀i, c i = f i) : CauchySeq α γ where
  toFun := f
  is_cauchy' := by
    rw [←funext hf]
    exact c.is_cauchy'

def copy_eq (c: CauchySeq α γ) (f: ℕ -> α) (hf: ∀i, c i = f i) : c.copy f hf = c := by
  ext; symm; apply hf

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

variable [LE α] [LT α] [IsPartialOrder α]

def IsPos (c: CauchySeq α γ) : Prop :=
  ∃B, 0 < B ∧ Eventually fun i => B < c i

protected def is_cauchy_eqv.IsPos (a b: CauchySeq α γ) (h: a ≈ b) : a.IsPos -> b.IsPos := sorry

def norm_pos_of_ne_zero (c: CauchySeq α γ) (h: ¬c ≈ 0) : ‖c‖.IsPos := by
  apply Classical.byContradiction; intro g
  replace g := not_exists.mp g
  simp [Eventually ,not_lt] at g
  replace g : ∀ε: γ, 0 < ε -> ∀i, ∃j, i ≤ j ∧ ‖c j‖  ≤ ε := g
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

protected def is_cauchy_eqv.safe_inv
  [IsLawfulMulNorm α γ]
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

instance : CheckedInv (CauchySeq α γ) (fun a => ¬a ≈ 0) where
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

instance : CheckedInv? (Completion α γ) where
  checked_inv := lift_with (P := (· ≠ 0)) (fun c hc =>
    have : ¬c ≈ 0 := fun g => hc (sound g)
    ofSeq c⁻¹?) <| by
    intro a b h pa
    dsimp
    apply sound
    apply is_cauchy_eqv.safe_inv
    assumption
    intro g; exact pa (sound g)

end CauchySeq

end
