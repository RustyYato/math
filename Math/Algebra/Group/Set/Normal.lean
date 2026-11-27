module

public import Math.Algebra.Group.Set.Defs
public import Math.Algebra.Group.Hom
public import Math.Algebra.Group.Congruence

import Math.Algebra.Group.Defs.Lemmas

namespace Math

namespace Subgroup

variable [GroupOps α] [IsGroup α]

@[expose] public def IsNormal (s: Subgroup α) : Prop :=
  ∀a ∈ s, ∀x, GroupEquiv.conj x a ∈ s

public theorem IsNormal.bot : IsNormal (α := α) ⊥ := by
  intro a rfl x
  rw [map_one]; rfl

public theorem IsNormal.top : IsNormal (α := α) ⊤ := by
  intro a _ x; trivial

@[expose] public def equivCon : { s: Subgroup α // IsNormal s } ≃ MulCon α where
  toFun s := {
    toRel a b := a / b ∈ s.val
    toEquiv := {
      refl a := by rw [div_self]; apply mem_one
      symm {x y} h := by
        rw [←div_inv]; apply mem_inv
        assumption
      trans {x y z} h g := by
        rw [←mul_one x, ←inv_mul_cancel y,
          ←mul_assoc, ←div_eq_mul_inv, mul_div_assoc]
        apply mem_mul <;> assumption
    }
    resp_mul a b c d a_eqv_c b_eqv_d := by
      rw [div_eq_mul_inv, ←inv_mul_inv_rev,
        mul_assoc, ←mul_assoc b, ←mul_assoc,
        ←div_eq_mul_inv b]
      rw [←mul_one a, ←inv_mul_cancel c,
        ←mul_assoc a, ←div_eq_mul_inv a, mul_assoc,
        mul_assoc]
      apply mem_mul; assumption
      rw [←mul_assoc]
      apply s.property (b / d) _ c
      assumption
  }
  invFun c := {
      val := {
        toSet := { Mem := c 1 }
        mem_one := c.toEquiv.refl _
        mem_inv {a} ha := by
          change c 1 a⁻¹
          rw [←one_inv]
          apply resp_inv
          assumption
        mem_mul {a b} ha hb := by
          change c 1 (a * b)
          rw [←mul_one 1]; apply resp_mul <;> assumption
      }
      property := by
        change ∀a (ha: c 1 a), _
        intro a ha x
        change c 1 _
        rw [GroupEquiv.apply_conj,
          ←mul_inv_cancel x]
        rw (occs := [1]) [←mul_one x]
        apply resp_mul
        apply resp_mul
        apply c.toEquiv.refl
        assumption
        apply c.toEquiv.refl
  }
  leftInv c := by
    apply DFunlike.ext
    intro x; ext y
    show c 1 _ ↔ _
    apply Iff.intro
    · intro h; apply c.toEquiv.symm
      show c y x
      have := resp_mul _ _ _ _ _ h (c.toEquiv.refl y)
      rwa [one_mul, div_mul_cancel] at this
    · intro h
      rw [←mul_inv_cancel y, div_eq_mul_inv]
      apply resp_mul
      apply c.toEquiv.symm
      assumption
      apply c.toEquiv.refl
  rightInv s := by
    ext; apply SetLike.ext
    intro x; dsimp
    show (1 / x) ∈ s.val ↔ _
    rw [one_div]
    apply Iff.intro
    intro h; rw [←inv_inv x]; apply mem_inv; assumption
    intro h; apply mem_inv; assumption

end Subgroup

namespace AddSubgroup

variable [AddGroupOps α] [IsAddGroup α]

@[expose] public def IsNormal (s: AddSubgroup α) : Prop :=
  ∀a ∈ s, ∀x, AddGroupEquiv.conj x a ∈ s

public theorem IsNormal.bot : IsNormal (α := α) ⊥ := by
  intro a rfl x
  rw [map_zero]; rfl

public theorem IsNormal.top : IsNormal (α := α) ⊤ := by
  intro a _ x; trivial

@[expose] public def equivCon : { s: AddSubgroup α // IsNormal s } ≃ AddCon α where
  toFun s := {
    toRel a b := a - b ∈ s.val
    toEquiv := {
      refl a := by rw [sub_self]; apply mem_zero
      symm {x y} h := by
        rw [←neg_sub]; apply mem_neg
        assumption
      trans {x y z} h g := by
        rw [←add_zero x, ←neg_add_cancel y,
          ←add_assoc, ←sub_eq_add_neg, add_sub_assoc]
        apply mem_add <;> assumption
    }
    resp_add a b c d a_eqv_c b_eqv_d := by
      rw [sub_eq_add_neg, ←neg_add_neg_rev,
        add_assoc, ←add_assoc b, ←add_assoc,
        ←sub_eq_add_neg b]
      rw [←add_zero a, ←neg_add_cancel c,
        ←add_assoc a, ←sub_eq_add_neg a, add_assoc,
        add_assoc]
      apply mem_add; assumption
      rw [←add_assoc]
      apply s.property (b - d) _ c
      assumption
  }
  invFun c := {
      val := {
        toSet := { Mem := c 0 }
        mem_zero := c.toEquiv.refl _
        mem_neg {a} ha := by
          change c 0 (-a)
          rw [←neg_zero]
          apply resp_neg
          assumption
        mem_add {a b} ha hb := by
          change c 0 (a + b)
          rw [←add_zero 0]; apply resp_add <;> assumption
      }
      property := by
        change ∀a (ha: c 0 a), _
        intro a ha x
        change c 0 _
        rw [AddGroupEquiv.apply_conj,
          ←add_neg_cancel x]
        rw (occs := [1]) [←add_zero x]
        apply resp_add
        apply resp_add
        apply c.toEquiv.refl
        assumption
        apply c.toEquiv.refl
  }
  leftInv c := by
    apply DFunlike.ext
    intro x; ext y
    show c 0 _ ↔ _
    apply Iff.intro
    · intro h; apply c.toEquiv.symm
      show c y x
      have := resp_add _ _ _ _ _ h (c.toEquiv.refl y)
      rwa [zero_add, sub_add_cancel] at this
    · intro h
      rw [←add_neg_cancel y, sub_eq_add_neg]
      apply resp_add
      apply c.toEquiv.symm
      assumption
      apply c.toEquiv.refl
  rightInv s := by
    ext; apply SetLike.ext
    intro x; dsimp
    show (0 - x) ∈ s.val ↔ _
    rw [zero_sub]
    apply Iff.intro
    intro h; rw [←neg_neg x]; apply mem_neg; assumption
    intro h; apply mem_neg; assumption

end AddSubgroup
