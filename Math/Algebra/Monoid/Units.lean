module

public import Math.Algebra.Monoid.Defs.Basic

namespace Math

@[ext]
public structure Unit (α: Type*) [Mul α] [One α] where
  val: α
  inv: α
  val_mul_inv: val * inv = 1
  inv_mul_val: inv * val = 1

@[ext]
public structure AddUnit (α: Type*) [Add α] [Zero α] where
  val: α
  neg: α
  val_add_neg: val + neg = 0
  neg_add_val: neg + val = 0

public class IsUnit {α: Type*} [Mul α] [One α] (a: α) where
  exists_unit : ∃u: Unit α, u.val = a

public class IsAddUnit {α: Type*} [Add α] [Zero α] (a: α) where
  exists_add_unit : ∃u: AddUnit α, u.val = a

export IsUnit (exists_unit)
export IsAddUnit (exists_add_unit)

namespace Unit

@[ext]
public theorem Unit.ext [Mul α] [One α]
  [IsLawfulOne α] [IsSemigroup α]
  (a b: Unit α) (h: a.val = b.val) : a = b := by
  ext; assumption
  rw [←one_mul a.inv, ←b.inv_mul_val, mul_assoc,
    ←h, a.val_mul_inv, mul_one]

@[ext]
public theorem AddUnit.ext [Add α] [Zero α]
  [IsLawfulZero α] [IsAddSemigroup α]
  (a b: AddUnit α) (h: a.val = b.val) : a = b := by
  ext; assumption
  rw [←zero_add a.neg, ←b.neg_add_val, add_assoc,
    ←h, a.val_add_neg, add_zero]

public instance [Mul α] [One α] (a: Unit α) : IsCommAt a.val a.inv where
  mul_comm := by rw [a.inv_mul_val, a.val_mul_inv]

public instance [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] : Mul (Unit α) where
  mul a b := {
    val := a.val * b.val
    inv := b.inv * a.inv
    val_mul_inv := by rw [←mul_assoc, mul_assoc a.val, b.val_mul_inv, mul_one, a.val_mul_inv]
    inv_mul_val := by rw [←mul_assoc, mul_assoc b.inv, a.inv_mul_val, mul_one, b.inv_mul_val]
  }

public instance [Mul α] [One α] [IsLawfulOne α] : One (Unit α) where
  one := {
    val := 1
    inv := 1
    val_mul_inv := by rw [mul_one]
    inv_mul_val := by rw [mul_one]
  }

public instance [MonoidOps α] [IsMonoid α] : Pow (Unit α) ℕ where
  pow a n := {
    val := a.val ^ n
    inv := a.inv ^ n
    val_mul_inv := by rw [←mul_pown, a.val_mul_inv, one_pown]
    inv_mul_val := by rw [←mul_pown, a.inv_mul_val, one_pown]
  }

@[simp] theorem mul_val [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a b: Unit α) : (a * b).val = a.val * b.val := rfl
@[simp] theorem mul_inv [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a b: Unit α) : (a * b).inv = b.inv * a.inv := rfl
@[simp] theorem one_val [Mul α] [One α] [IsLawfulOne α] : Unit.val 1 = (1: α) := rfl
@[simp] theorem one_inv [Mul α] [One α] [IsLawfulOne α] : Unit.inv 1 = (1: α) := rfl
@[simp] theorem pown_val [MonoidOps α] [IsMonoid α] (a: Unit α) (n: ℕ) : (a ^ n).val = a.val ^ n := rfl
@[simp] theorem pown_inv [MonoidOps α] [IsMonoid α] (a: Unit α) (n: ℕ) : (a ^ n).inv = a.inv ^ n := rfl

public instance [MonoidOps α] [IsMonoid α] : IsMonoid (Unit α) where
  mul_assoc _ _ _ := by ext <;> (dsimp; rw [mul_assoc])
  mul_one _ := by ext <;> dsimp; rw [mul_one]
  one_mul _ := by ext <;> dsimp; rw [one_mul]
  pown_zero a := by ext <;> (dsimp; apply pown_zero)
  pown_succ a n := by ext <;> dsimp; apply pown_succ

end Unit

namespace AddUnit

public instance [Add α] [Zero α] (a: AddUnit α) : IsAddCommAt a.val a.neg where
  add_comm := by rw [a.neg_add_val, a.val_add_neg]

public instance [Add α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α] : Add (AddUnit α) where
  add a b := {
    val := a.val + b.val
    neg := b.neg + a.neg
    val_add_neg := by rw [←add_assoc, add_assoc a.val, b.val_add_neg, add_zero, a.val_add_neg]
    neg_add_val := by rw [←add_assoc, add_assoc b.neg, a.neg_add_val, add_zero, b.neg_add_val]
  }

public instance [Add α] [Zero α] [IsLawfulZero α] : Zero (AddUnit α) where
  zero := {
    val := 0
    neg := 0
    val_add_neg := by rw [add_zero]
    neg_add_val := by rw [add_zero]
  }

public instance [AddMonoidOps α] [IsAddMonoid α] : SMul ℕ (AddUnit α) where
  smul n a := {
    val := n • a.val
    neg := n • a.neg
    val_add_neg := by rw [←nsmul_add, a.val_add_neg, nsmul_zero]
    neg_add_val := by rw [←nsmul_add, a.neg_add_val, nsmul_zero]
  }

@[simp] theorem add_val [Add α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α] (a b: AddUnit α) : (a + b).val = a.val + b.val := rfl
@[simp] theorem add_neg [Add α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α] (a b: AddUnit α) : (a + b).neg = b.neg + a.neg := rfl
@[simp] theorem zero_val [Add α] [Zero α] [IsLawfulZero α] : AddUnit.val 0 = (0: α) := rfl
@[simp] theorem zero_neg [Add α] [Zero α] [IsLawfulZero α] : AddUnit.neg 0 = (0: α) := rfl
@[simp] theorem smuln_val [AddMonoidOps α] [IsAddMonoid α] (a: AddUnit α) (n: ℕ) : (n • a).val = n • a.val := rfl
@[simp] theorem smuln_neg [AddMonoidOps α] [IsAddMonoid α] (a: AddUnit α) (n: ℕ) : (n • a).neg = n • a.neg := rfl

public instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (AddUnit α) where
  add_assoc _ _ _ := by ext <;> (dsimp; rw [add_assoc])
  add_zero _ := by ext <;> dsimp; rw [add_zero]
  zero_add _ := by ext <;> dsimp; rw [zero_add]
  zero_nsmul a := by ext <;> (dsimp; apply zero_nsmul)
  succ_nsmul a n := by ext <;> dsimp; apply succ_nsmul

end AddUnit

public instance  [Mul α] [One α] [IsLawfulOne α] : IsUnit (α := α) 1 where
  exists_unit := ⟨1, rfl⟩

public instance  [Add α] [Zero α] [IsLawfulZero α] : IsAddUnit (α := α) 0 where
  exists_add_unit := ⟨0, rfl⟩
