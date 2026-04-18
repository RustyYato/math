import LeanMath.Algebra.Group.Normal.Defs

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α] [RelLike C α] [IsMulCon C]

def ofCon (c: C) : NormalSubgroup α where
  toSet := { Mem := (c 1 ·) }
  mem_one := Relation.refl (R := c) _
  mem_mul := by
    intro a b ha hb
    dsimp at ha hb; dsimp
    rw [←mul_one 1]
    apply resp_mul <;> assumption
  mem_inv := by
    intro a ha; dsimp
    rw [←one_inv]
    apply resp_inv
    assumption
  mem_conj := by
    intro a x h
    dsimp at *
    rw [←map_one (conj x)]
    apply resp_mul
    apply resp_mul; rfl
    assumption; rfl

def toCon (s: NormalSubgroup α) : MulCon α where
  toFun a b := a / b ∈ s
  eqv := {
    refl x := by rw [div_self]; apply mem_one
    symm {x y} h := by
      rw [←inv_div]
      apply mem_inv
      assumption
    trans := by
      intro x y z h g
      rw [←mul_one x, ←inv_mul_cancel y, ←mul_assoc,
        ←div_eq_mul_inv, mul_div_assoc]
      apply mem_mul
      assumption
      assumption
  }
  resp_mul := by
    intro a b c d ha hb
    rw [div_eq_mul_inv, inv_mul_rev,
      ←mul_one a, ←inv_mul_cancel c,
        mul_assoc a, mul_assoc a,
        mul_assoc c⁻¹, mul_assoc c⁻¹,
        ←mul_assoc a]
    apply mem_mul
    · rw [←div_eq_mul_inv]
      assumption
    · rw [mul_assoc, ←mul_assoc b, ←div_eq_mul_inv b, ←mul_assoc]
      apply mem_conj
      assumption

def eqv : NormalSubgroup α ≃ MulCon α where
  toFun := toCon
  invFun := ofCon
  leftInv c := by
    apply DFunLike.ext; intro a; ext b
    show c 1 (a / b) ↔ _
    apply Iff.intro
    intro h
    have := resp_mul c h (Relation.refl b)
    rw [one_mul, div_mul_assoc, inv_mul_cancel, mul_one] at this
    apply Relation.symm; assumption
    intro h
    rw [←div_self b]
    apply resp_div
    apply Relation.symm; assumption
    rfl
  rightInv s := by
    apply SetLike.ext
    intro x
    show 1 / x ∈ s ↔ _
    rw [one_div]
    apply Iff.intro
    rw (occs := [2]) [←inv_inv x]
    apply mem_inv
    apply mem_inv

end NormalSubgroup
