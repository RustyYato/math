import LeanMath.Data.Complex.Cauchy
import LeanMath.Data.Fintype.Algebra.Monoid
import LeanMath.Data.RsqrtD.Char
import LeanMath.Data.Nat.Factorial

variable [LEM]

namespace Complex

def exp_sum (s: ComplexRational) (n: ℕ) : ComplexRational :=
  ∑i: Fin n, (s ^ i.val) /? i.val.fact

def exp_sum' (s: ComplexRational) (n o: ℕ) : ComplexRational :=
  ∑i: Fin n, (s ^ (i.val + o)) /? (i.val + o).fact

def exp_sum_eq_exp_sum' : exp_sum s n = exp_sum' s n 0 := rfl

def eqv_exp (a b: CauchySeq ComplexRational ℚ) (h: a ≈ b) : is_cauchy_eqv (fun i => exp_sum (a i) i) (fun i => exp_sum (b i) i) := by
  intro ε εpos
  dsimp
  have ⟨n, hn⟩ := archimedean_iff_nat_lt.mp inferInstance ε⁻¹?
  have : n ≠ 0 := by
    intro rfl;
    rw [natCast_zero] at hn
    exact Relation.asymm hn (pos_inv? _ εpos)
  replace hn : (n: ℚ)⁻¹? < _ := inv?_lt_inv? (pos_inv? _ εpos) hn
  rw [inv?_inv?] at hn
  have k := n
  exists k; intro i j hi hj
  rcases le_total i j with h | h
  · sorry
  · sorry

-- def exp' (s: CauchySeq ComplexRational ℚ) : CauchySeq ComplexRational ℚ where
--   toFun i := exp_sum (s i) i
--   is_cauchy' := by
--     apply eqv_exp
--     rfl

-- def exp (s: ℂ) : ℂ :=
--   CauchySeq.lift (fun s => Complex.equivCauchy.symm (exp' s).ofSeq) (by
--     intro a b h
--     dsimp; congr 1; apply CauchySeq.sound
--     apply eqv_exp
--     assumption) (Complex.equivCauchy s)

end Complex
