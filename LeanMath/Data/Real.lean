import LeanMath.Data.CauSeq.Defs
import LeanMath.Data.Rational.Norm
import LeanMath.Algebra.Algebra.Ring

variable [LEM]

def Real := CauchySeq.Completion ℚ ℚ

notation "ℝ" => Real

namespace Real

section

-- unseal Real

instance : FieldOps ℝ := inferInstanceAs (FieldOps (CauchySeq.Completion ℚ ℚ))
instance : IsField ℝ := inferInstanceAs (IsField (CauchySeq.Completion ℚ ℚ))
instance : LT ℝ := inferInstanceAs (LT (CauchySeq.Completion ℚ ℚ))
instance : LE ℝ := inferInstanceAs (LE (CauchySeq.Completion ℚ ℚ))
instance : IsZeroLEOne ℝ := inferInstanceAs (IsZeroLEOne (CauchySeq.Completion ℚ ℚ))
instance : IsLinearOrder ℝ := inferInstanceAs (IsLinearOrder (CauchySeq.Completion ℚ ℚ))
instance : IsStrictOrderedSemiring ℝ := inferInstanceAs (IsStrictOrderedSemiring (CauchySeq.Completion ℚ ℚ))

instance : SMul ℚ ℝ := inferInstanceAs (SMul ℚ (CauchySeq.Completion ℚ ℚ))
instance : AlgebraMap ℚ ℝ := inferInstanceAs (AlgebraMap ℚ (CauchySeq.Completion ℚ ℚ))
instance : IsAlgebra ℚ ℝ := inferInstanceAs (IsAlgebra ℚ (CauchySeq.Completion ℚ ℚ))
instance : IsModule ℚ ℝ := inferInstance

def ofRat : ℚ ↪+* ℝ where
    toRingHom := algebraMap ℚ
    inj := inj (algebraMap ℚ (α := ℝ))

instance : AlgebraMap ℤ ℝ := inferInstance
instance : IsAlgebra ℤ ℝ := inferInstance
instance : AlgebraMap ℕ ℝ := inferInstance
instance : IsAlgebra ℕ ℝ := inferInstance

instance : Norm ℝ ℝ := inferInstanceAs (Norm (CauchySeq.Completion ℚ ℚ) (CauchySeq.Completion ℚ ℚ))
instance : IsLawfulAbs ℝ := inferInstanceAs (IsLawfulAbs (CauchySeq.Completion ℚ ℚ))

end

instance : HasChar ℝ 0 := HasChar.of_ring_emb ofRat

end Real
