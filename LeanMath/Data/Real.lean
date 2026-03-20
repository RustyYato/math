import LeanMath.Data.CauSeq.Defs
import LeanMath.Data.Rational.Norm

@[irreducible]
def Real := CauchySeq.Completion ℚ ℚ

notation "ℝ" => Real

namespace Real

section

unseal Real

variable [LEM]

instance : FieldOps ℝ := inferInstanceAs (FieldOps (CauchySeq.Completion ℚ ℚ))
instance : IsField ℝ := inferInstanceAs (IsField (CauchySeq.Completion ℚ ℚ))
instance : LT ℝ := inferInstanceAs (LT (CauchySeq.Completion ℚ ℚ))
instance : LE ℝ := inferInstanceAs (LE (CauchySeq.Completion ℚ ℚ))
instance : IsLinearOrder ℝ := inferInstanceAs (IsLinearOrder (CauchySeq.Completion ℚ ℚ))
instance : IsStrictOrderedSemiring ℝ := inferInstanceAs (IsStrictOrderedSemiring (CauchySeq.Completion ℚ ℚ))

instance : SMul ℚ ℝ := inferInstanceAs (SMul ℚ (CauchySeq.Completion ℚ ℚ))
instance : AlgebraMap ℚ ℝ := inferInstanceAs (AlgebraMap ℚ (CauchySeq.Completion ℚ ℚ))
instance : IsAlgebra ℚ ℝ := inferInstanceAs (IsAlgebra ℚ (CauchySeq.Completion ℚ ℚ))
instance : IsModule ℚ ℝ := inferInstance

def ofRat : ℚ ↪+* ℝ where
    toRingHom := algebraMap ℚ
    inj := inj (algebraMap ℚ (α := ℝ))

#print axioms ofRat

instance : AlgebraMap ℤ ℝ where
    toAlgebraMap := intCastHom
instance : IsAlgebra ℤ ℝ where
    commutes _ _ := by rw [mul_comm]
    smul_def r x := by
        show (r: ℚ) • x = _
        rw [smul_def]
        rfl

instance : AlgebraMap ℕ ℝ where
    toAlgebraMap := natCastHom
instance : IsAlgebra ℕ ℝ where
    commutes _ _ := by rw [mul_comm]
    smul_def r x := by
        show (r: ℚ) • x = _
        rw [smul_def]
        rfl

end

instance : HasChar ℝ 0 := HasChar.of_ring_emb ofRat

end Real
