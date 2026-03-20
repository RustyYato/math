import LeanMath.Data.CauSeq.Defs
import LeanMath.Data.Rational.Norm

@[irreducible]
def Real := CauchySeq.Completion ℚ ℚ

notation "ℝ" => Real

namespace Real

section

unseal Real

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
    inj := CauchySeq.Completion.const_inj

end

instance : HasChar ℝ 0 := HasChar.of_ring_emb ofRat

end Real
