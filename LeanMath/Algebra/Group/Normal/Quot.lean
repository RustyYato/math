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
  toFun a b := b / a ∈ s
  eqv := {
    refl x := by rw [div_self]; apply mem_one
    symm {x y} h := by
      rw [←inv_div]
      apply mem_inv
      assumption
    trans := by
      intro x y z h g
      rw [←mul_one z, ←inv_mul_cancel y, ←mul_assoc,
        ←div_eq_mul_inv, mul_div_assoc]
      apply mem_mul
      assumption
      assumption
  }
  resp_mul := by
    intro a b c d ha hb
    rw [div_eq_mul_inv, inv_mul_rev,
      ←mul_one c, ←inv_mul_cancel a,
        mul_assoc c, mul_assoc c,
        mul_assoc a⁻¹, mul_assoc a⁻¹,
        ←mul_assoc c]
    apply mem_mul
    · rw [←div_eq_mul_inv]
      assumption
    · rw [mul_assoc, ←mul_assoc d, ←div_eq_mul_inv d, ←mul_assoc]
      apply mem_conj
      assumption

def eqv : NormalSubgroup α ≃ MulCon α where
  toFun := toCon
  invFun := ofCon
  leftInv c := by
    apply DFunLike.ext; intro a; ext b
    show c 1 (b / a) ↔ _
    apply Iff.intro
    intro h
    have := resp_mul c h (Relation.refl a)
    rw [one_mul, div_mul_assoc, inv_mul_cancel, mul_one] at this
    assumption
    intro h
    rw [←div_self a]
    apply resp_div
    assumption
    rfl
  rightInv s := by
    apply SetLike.ext
    intro x
    show x / 1 ∈ s ↔ _
    rw [div_one]

end NormalSubgroup

namespace NormalAddSubgroup

variable [AddGroupOps α] [IsAddGroup α] [RelLike C α] [IsAddCon C]

def ofCon (c: C) : NormalAddSubgroup α where
  toSet := { Mem := (c 0 ·) }
  mem_zero := Relation.refl (R := c) _
  mem_add := by
    intro a b ha hb
    dsimp at ha hb; dsimp
    rw [←add_zero 0]
    apply resp_add <;> assumption
  mem_neg := by
    intro a ha; dsimp
    rw [←neg_zero]
    apply resp_neg
    assumption
  mem_add_conj := by
    intro a x h
    dsimp at *
    rw [←map_zero (add_conj x)]
    apply resp_add
    apply resp_add; rfl
    assumption; rfl

def toCon (s: NormalAddSubgroup α) : AddCon α where
  toFun a b := b - a ∈ s
  eqv := {
    refl x := by rw [sub_self]; apply mem_zero
    symm {x y} h := by
      rw [←neg_sub]
      apply mem_neg
      assumption
    trans := by
      intro x y z h g
      rw [←add_zero z, ←neg_add_cancel y, ←add_assoc,
        ←sub_eq_add_neg, add_sub_assoc]
      apply mem_add
      assumption
      assumption
  }
  resp_add := by
    intro a b c d ha hb
    rw [sub_eq_add_neg, neg_add_rev,
      ←add_zero c, ←neg_add_cancel a,
        add_assoc c, add_assoc c,
        add_assoc (-a), add_assoc (-a),
        ←add_assoc c]
    apply mem_add
    · rw [←sub_eq_add_neg]
      assumption
    · rw [add_assoc, ←add_assoc d, ←sub_eq_add_neg d, ←add_assoc]
      apply mem_add_conj
      assumption

def eqv : NormalAddSubgroup α ≃ AddCon α where
  toFun := toCon
  invFun := ofCon
  leftInv c := by
    apply DFunLike.ext; intro a; ext b
    show c 0 (b - a) ↔ _
    apply Iff.intro
    intro h
    have := resp_add c h (Relation.refl a)
    rw [zero_add, sub_add_assoc, neg_add_cancel, add_zero] at this
    assumption
    intro h
    rw [←sub_self a]
    apply resp_sub
    assumption
    rfl
  rightInv s := by
    apply SetLike.ext
    intro x
    show x - 0 ∈ s ↔ _
    rw [sub_zero]

end NormalAddSubgroup
