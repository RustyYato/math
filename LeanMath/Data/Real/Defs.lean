import LeanMath.Data.CauSeq.Defs
import LeanMath.Data.Rational.Norm
import LeanMath.Algebra.Algebra.Ring

structure Real where
  ofCauchySeq :: toCauchySeq : CauchySeq.Completion ℚ ℚ

notation "ℝ" => Real

namespace Real

def equivCauchySeq : ℝ ≃ CauchySeq.Completion ℚ ℚ where
  toFun := Real.toCauchySeq
  invFun := Real.ofCauchySeq
  leftInv _ := rfl
  rightInv _ := rfl

instance : RingOps ℝ := OfEquiv.instRingOps equivCauchySeq
instance : IsRing ℝ := OfEquiv.instIsRing equivCauchySeq

instance : LT ℝ := OfEquiv.instLT equivCauchySeq
instance : LE ℝ := OfEquiv.instLE equivCauchySeq
instance : IsPartialOrder ℝ := OfEquiv.instIsPartialOrder equivCauchySeq

instance : IsZeroLEOne ℝ := OfEquiv.instIsZeroLEOne equivCauchySeq
instance : IsOrderedSemiring ℝ := OfEquiv.instIsOrderedSemiring equivCauchySeq
instance : IsZeroNeOne ℝ := OfEquiv.IsZeroNeOne equivCauchySeq

instance : SMul ℚ ℝ := OfEquiv.smul equivCauchySeq _
instance : AlgebraMap ℚ ℝ := OfEquiv.algebraMap equivCauchySeq
instance : IsModule ℚ ℝ := OfEquiv.instIsModule equivCauchySeq
instance : IsAlgebra ℚ ℝ := OfEquiv.instIsAlgebra (R := ℚ) equivCauchySeq

instance : AlgebraMap ℤ ℝ := inferInstance
instance : IsAlgebra ℤ ℝ := inferInstance
instance : AlgebraMap ℕ ℝ := inferInstance
instance : IsAlgebra ℕ ℝ := inferInstance

instance : Norm ℝ ℝ := OfEquiv.NormSelf.instNorm equivCauchySeq
instance : IsLawfulAbs ℝ := OfEquiv.NormSelf.instIsLawfulAbs equivCauchySeq
instance : IsAbsMax ℝ := OfEquiv.NormSelf.instIsAbsMax equivCauchySeq

instance : IsLawfulNorm ℝ ℝ := inferInstance
instance : IsDistributiveAction ℝ ℝ := inferInstance

def ringEquivCauchySeq : ℝ ≃+* CauchySeq.Completion ℚ ℚ :=
  OfEquiv.ringEquiv equivCauchySeq

def equivCauchySeq_eq_ringEquivCauchySeq : (equivCauchySeq: ℝ -> _) = (ringEquivCauchySeq: ℝ -> _) :=
  rfl

def cau_ind {motive: ℝ -> Prop} (ofCauchy: ∀c, motive (ringEquivCauchySeq.symm (CauchySeq.ofSeq c))) (x: ℝ) : motive x := by
  induction h:ringEquivCauchySeq x using CauchySeq.ind with | _ x' =>
  rw [←RingEquiv.coe_symm ringEquivCauchySeq (x := x)]
  rw [h]; apply ofCauchy

def ofRat : ℚ ↪+* ℝ := RingEmbedding.ofFieldHom (algebraMap ℚ)

instance : HasChar ℝ 0 := HasChar.of_ring_emb ofRat

variable [LEM]

instance : FieldOps ℝ := OfEquiv.instFieldOps equivCauchySeq
instance : IsField ℝ := OfEquiv.instIsField equivCauchySeq

instance : IsLinearOrder ℝ := OfEquiv.instIsLinearOrder equivCauchySeq
instance : IsStrictOrderedSemiring ℝ := OfEquiv.instIsStrictOrderedSemiring equivCauchySeq

instance : Min ℝ where
    min a b := (a + b - ‖a - b‖) /? (2: ℕ)
instance : Max ℝ where
    max a b := (a + b + ‖a - b‖) /? (2: ℕ)

private def min_def (a b: ℝ) : a ⊓ b = (a + b - ‖a - b‖) /? (2: ℕ) := rfl
private def max_def (a b: ℝ) : a ⊔ b = (a + b + ‖a - b‖) /? (2: ℕ) := rfl

private protected def max_comm (a b: ℝ) : a ⊔ b = b ⊔ a := by
  rw [max_def, max_def, add_comm a, norm_sub]
private protected def min_comm (a b: ℝ) : a ⊓ b = b ⊓ a := by
  rw [min_def, min_def, add_comm a, norm_sub]
private protected def min_le_left (a b: ℝ) : a ⊓ b ≤ a := by
    rw [min_def]
    have := mul_le_mul_of_nonneg_right (b := a * (2: ℕ)) (a := a + b - ‖a - b‖) (c := (2: ℕ)⁻¹?)
    rw [mul_assoc, mul_inv?_cancel, mul_one, ←div?_eq_mul_inv?] at this
    apply this
    · rw [←nsmul_eq_mul_natCast, succ_nsmul, one_nsmul, add_sub_assoc]
      apply add_le_add_left
      apply le_of_add_le_add_right
      rw [sub_add_assoc, neg_add_cancel, add_zero]
      apply le_of_add_le_add_left
      rw [←add_assoc, neg_add_cancel a, zero_add, add_comm, norm_sub, ←sub_eq_add_neg]
      induction a using cau_ind with | _ a =>
      induction b using cau_ind with | _ b =>
      apply CauchySeq.le_of_eventually_le
      exists 0; intro i hi
      show b i - a i ≤ ‖b i - a i‖
      rw [abs_eq_max]
      apply left_le_max
    · apply le_of_lt
      apply pos_inv?
      apply pos_natCast

private protected def left_le_max (a b: ℝ) : a ≤ a ⊔ b := by
    rw [max_def]
    have := mul_le_mul_of_nonneg_right (a := a * (2: ℕ)) (b := a + b + ‖a - b‖) (c := (2: ℕ)⁻¹?)
    rw [mul_assoc, mul_inv?_cancel, mul_one, ←div?_eq_mul_inv?] at this
    apply this
    · rw [←nsmul_eq_mul_natCast, succ_nsmul, one_nsmul, add_assoc]
      apply add_le_add_left
      rw [add_comm]
      apply le_of_add_le_add_right
      rw [add_assoc, add_neg_cancel b, add_zero, ←sub_eq_add_neg]
      induction a using cau_ind with | _ a =>
      induction b using cau_ind with | _ b =>
      apply CauchySeq.le_of_eventually_le
      exists 0; intro i hi
      show a i - b i ≤ ‖a i - b i‖
      rw [abs_eq_max]
      apply left_le_max
    · apply le_of_lt
      apply pos_inv?
      apply pos_natCast

private protected def max_eq_of_le {a b: ℝ} (h: a ≤ b) : a ⊔ b = b := by
  rw [max_def, norm_sub, abs_eq_of_nonneg, add_comm, sub_add_assoc, ←add_assoc (-a), neg_add_cancel, zero_add]
  rw (occs := [1]) [←one_nsmul b, ←succ_nsmul, nsmul_eq_mul_natCast, mul_div?_assoc, div?_self, mul_one]
  apply le_of_add_le_add_right
  rwa [sub_add_assoc, neg_add_cancel, add_zero, zero_add]
private protected def max_eq (a b: ℝ) : a ⊔ b = a ∨ a ⊔ b = b := by
  rcases le_total a b with h | h
  right; rw [max_eq_of_le h]
  left; rw [max_comm, max_eq_of_le h]

private protected def min_eq_of_le {a b: ℝ} (h: a ≤ b) : a ⊓ b = a := by
  rw [min_def, norm_sub, abs_eq_of_nonneg, sub_eq_add_neg, neg_sub, sub_eq_add_neg, add_assoc, add_left_comm b, add_neg_cancel, add_zero]
  rw (occs := [1]) [←one_nsmul a, ←succ_nsmul, nsmul_eq_mul_natCast, mul_div?_assoc, div?_self, mul_one]
  apply le_of_add_le_add_right
  rwa [sub_add_assoc, neg_add_cancel, add_zero, zero_add]
private protected def min_eq (a b: ℝ) : a ⊓ b = a ∨ a ⊓ b = b := by
  rcases le_total a b with h | h
  left; rw [min_eq_of_le h]
  right; rw [min_comm, min_eq_of_le h]

instance : IsLattice ℝ where
    left_le_max := left_le_max _ _
    right_le_max := by intro a b; rw [max_comm]; apply left_le_max
    max_le := by
      intro x a b ha hb
      rcases max_eq a b with h | h <;> rwa [h]
    min_le_left := min_le_left _ _
    min_le_right := by intro a b; rw [min_comm]; apply min_le_left
    le_min := by
      intro x a b ha hb
      rcases min_eq a b with h | h <;> rwa [h]

unsafe scoped instance Repr.Float.instRepr : Repr ℝ where
  reprPrec r n :=
    let f := (CauchySeq.Completion.toQuot r.toCauchySeq).lift (fun x => x) lcProof
    repr (Array.ofFn (n := bif n == 0 then 5 else n) fun i => (f i).approx)

unsafe scoped instance Repr.Rat.instRepr : Repr ℝ where
  reprPrec r n :=
    let f := (CauchySeq.Completion.toQuot r.toCauchySeq).lift (fun x => x) lcProof
    repr (Array.ofFn (n := bif n == 0 then 5 else n) fun i => f i)

def lift (f: CauchySeq ℚ ℚ -> α) (hf: ∀a b, a ≈ b -> f a = f b) : ℝ -> α :=
  fun r => CauchySeq.lift f hf (Real.ringEquivCauchySeq r)

def recSeq
  {motive: ℝ -> Sort u}
  (f: ∀s: CauchySeq ℚ ℚ, motive (ofCauchySeq s.ofSeq))
  (hf: ∀a b, a ≈ b -> HEq (f a) (f b)) (r: ℝ) : motive r :=
   r.toCauchySeq.toQuot.hrecOn
    (motive := fun q => motive (ofCauchySeq (CauchySeq.Completion.ofQuot q)))
    (fun x => f x) hf

def lift_with
  (r: ℝ)
  (f: ∀s: CauchySeq ℚ ℚ, r = ofCauchySeq s.ofSeq -> α)
  (hf: ∀a b ha hb, f a ha = f b hb) : α :=
   r.recSeq (motive := fun s => r = s -> α)
    (fun s hs => f s hs)
    (by
      intro a b h; dsimp
      apply Function.hfunext
      congr 1; rw [CauchySeq.sound h]
      intro ha hb heq
      apply heq_of_eq
      apply hf)
    rfl

def sound (a b: CauchySeq ℚ ℚ) : a ≈ b -> Real.ringEquivCauchySeq.symm a.ofSeq = Real.ringEquivCauchySeq.symm b.ofSeq := by
  intro h; rw [CauchySeq.sound h]

def offset (n: ℕ) : ℝ -> ℝ :=
  lift (fun r => ringEquivCauchySeq.symm <| (r.offset n).ofSeq) <| by
    intro a b h
    apply sound
    apply CauchySeq.is_cauchy_eqv.offset
    assumption

noncomputable instance (a b: ℝ) : Decidable (a ≤ b) :=
  open UniqueChoice in inferInstance
noncomputable instance (a b: ℝ) : Decidable (a < b) :=
  open UniqueChoice in inferInstance
noncomputable instance (a b: ℝ) : Decidable (a = b) :=
  open UniqueChoice in inferInstance

end Real
