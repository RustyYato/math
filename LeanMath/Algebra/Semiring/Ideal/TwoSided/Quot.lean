import LeanMath.Algebra.Semiring.Ideal.TwoSided.Defs

variable [SemiringOps α] [IsSemiring α]

section

variable [RelLike C α] [IsMulCon C] [IsAddCon C]

def Ideal.ofCon (c: C) : Ideal α where
  toSet := { Mem := (c 0 ·) }
  mem_zero := (IsCon.eqv c).refl 0
  mem_add := by
    intro a b ha hb
    show c 0 (a + b)
    rw [←add_zero 0]
    apply resp_add
    assumption
    assumption
  mem_left_mul := by
    intro a k ha
    show c 0 (k * a)
    rw [←mul_zero k]
    apply resp_mul
    apply (IsCon.eqv c).refl
    assumption
  mem_right_mul := by
    intro a k ha
    show c 0 (a * k)
    rw [←zero_mul k]
    apply resp_mul
    assumption
    apply (IsCon.eqv c).refl

end
