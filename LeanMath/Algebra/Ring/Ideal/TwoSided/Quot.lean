import LeanMath.Algebra.Semiring.Ideal.TwoSided.Quot
import LeanMath.Algebra.Ring.Ideal.TwoSided.Defs
import LeanMath.Algebra.Ring.Defs

variable [RingOps α] [IsRing α]

def Ideal.toCon (i: Ideal α) : RingCon α where
  toFun a b := a - b ∈ i
  eqv := {
    refl a := by
      rw [sub_self]
      apply mem_zero
    symm {x y} h := by
      rw [←neg_sub]
      apply mem_neg
      assumption
    trans {x y z} h g := by
      rw [←add_zero x, ←neg_add_cancel y, ←add_assoc,
        add_sub_assoc, ←sub_eq_add_neg]
      apply mem_add
      assumption
      assumption
  }
  resp_add {a b c d} h g := by
    rw [add_comm c, sub_add, add_sub_comm, add_sub_assoc]
    apply mem_add
    assumption
    assumption
  resp_mul {a b c d} h g := by
    rw [←add_zero (a * b), ←neg_add_cancel (a * d),
      ←add_assoc, ←sub_eq_add_neg, add_sub_assoc,
      ←mul_sub, ←sub_mul]
    apply mem_add
    apply mem_left_mul
    assumption
    apply mem_right_mul
    assumption

def Ideal.equivCon : Ideal α ≃ RingCon α where
  toFun := Ideal.toCon
  invFun := Ideal.ofCon
  leftInv c := by
    apply DFunLike.ext
    intro x; ext y
    show c _ _ ↔ _
    apply Iff.intro
    · intro h
      have := resp_add c h ((IsCon.eqv c).refl y)
      apply (IsCon.eqv c).symm
      rwa [zero_add, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] at this
    · intro h
      have := resp_add c h ((IsCon.eqv c).refl (-y))
      apply (IsCon.eqv c).symm
      rwa [←sub_eq_add_neg, add_neg_cancel] at this
  rightInv i := by
    apply SetLike.ext
    intro x
    show _ ∈ i ↔ _
    rw [←neg_sub, sub_zero]
    apply Iff.intro
    rw (occs := [2]) [←neg_neg x]
    apply mem_neg
    apply mem_neg
