import LeanMath.Data.Rational.Defs
import LeanMath.Data.Nat.Prod
import LeanMath.Data.Countable.Defs

namespace Rational

private def Fract.equiv_nat' : Fract ≃ (ℤ × ℕ) where
  toFun f := (f.num, f.den - 1)
  invFun f := {
    num := f.fst
    den := f.snd + 1
    den_ne_zero := Nat.succ_ne_zero _
  }
  leftInv _ := rfl
  rightInv f := by
    obtain ⟨n, d, _⟩ := f
    match d with
    | d + 1 => rfl

def Fract.equivNat : Fract ≃ ℕ :=
  Equiv.trans Fract.equiv_nat' <|
  (Equiv.prod_congr Equiv.int_equiv_nat.symm (Equiv.id _)).symm.trans
  Equiv.nat_equiv_nat_prod_nat.symm

def equivSubtypeFract : ℚ ≃ { f: Fract // f.is_reduced } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

instance : Encodable Fract :=
  Encodable.ofEquiv Fract.equivNat.symm
instance : Encodable ℚ :=
  Encodable.ofEquiv equivSubtypeFract.symm

instance : IsCountable Fract := inferInstance
instance : IsCountable ℚ := inferInstance

end Rational
