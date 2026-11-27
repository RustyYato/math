module

public import Math.Algebra.Group.Defs.Hom
public import Math.Algebra.Monoid.Hom
import Math.Algebra.Group.Defs.Lemmas

namespace Math

public def AddGroupEquiv.conj [AddGroupOps α] [IsAddGroup α] (x: α) : α ≃+ α where
  toFun a := x + a + -x
  invFun a := -x + a + x
  leftInv a := by dsimp; rw [←add_assoc x, ←add_assoc x, add_neg_cancel, zero_add, add_assoc, add_neg_cancel, add_zero]
  rightInv a := by dsimp; rw [←add_assoc (-x), ←add_assoc (-x), neg_add_cancel, zero_add, add_assoc, neg_add_cancel, add_zero]
  map_zero := by rw [add_zero, add_neg_cancel]
  map_add a b := by
    rw [add_assoc x a, add_assoc x (_ + -x), add_assoc a (-x),
      ←add_assoc (-x), ←add_assoc (-x), neg_add_cancel, zero_add]
    repeat rw [add_assoc]

public def GroupEquiv.conj [GroupOps α] [IsGroup α] (x: α) : α ≃* α where
  toFun a := x * a * x⁻¹
  invFun a := x⁻¹ * a * x
  leftInv := (AddGroupEquiv.conj (AddOfMul.mk x)).leftInv
  rightInv := (AddGroupEquiv.conj (AddOfMul.mk x)).rightInv
  map_one := (AddGroupEquiv.conj (AddOfMul.mk x)).map_zero
  map_mul := (AddGroupEquiv.conj (AddOfMul.mk x)).map_add

@[simp] theorem AddGroupEquiv.apply_conj [AddGroupOps α] [IsAddGroup α] (x a: α) : AddGroupEquiv.conj x a = x + a + -x := rfl
@[simp] theorem AddGroupEquiv.apply_symm_conj [AddGroupOps α] [IsAddGroup α] (x a: α) : (AddGroupEquiv.conj x).symm a = -x + a + x := rfl
@[simp] theorem AddGroupEquiv.conj_symm [AddGroupOps α] [IsAddGroup α] (x: α) : (AddGroupEquiv.conj x).symm = AddGroupEquiv.conj (-x) := by
  ext i; dsimp; rw [neg_neg]

@[simp] theorem GroupEquiv.apply_conj [GroupOps α] [IsGroup α] (x a: α) : GroupEquiv.conj x a = x * a * x⁻¹ := rfl
@[simp] theorem GroupEquiv.apply_symm_conj [GroupOps α] [IsGroup α] (x a: α) : (GroupEquiv.conj x).symm a = x⁻¹ * a * x := rfl
@[simp] theorem GroupEquiv.conj_symm [GroupOps α] [IsGroup α] (x: α) : (GroupEquiv.conj x).symm = GroupEquiv.conj (x⁻¹) := by
  ext i; dsimp; rw [inv_inv]
