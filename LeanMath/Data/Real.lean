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
instance : IsModule ℚ ℝ := inferInstanceAs (IsModule ℚ (CauchySeq.Completion ℚ ℚ))

end

unseal Real in def ofRat : ℚ ↪+* ℝ where
    toFun := CauchySeq.Completion.const
    inj := CauchySeq.Completion.const_inj
    map_zero := rfl
    map_one := rfl
    map_add _ _ := rfl
    map_mul _ _ := rfl

instance : HasChar ℝ 0 := HasChar.of_ring_emb ofRat

end Real
