module

public import Math.Algebra.Monoid.Defs.Basic

namespace Math

section Property

public class IsLawfulOneSMul (R α: Type*) [One R] [SMul R α] where
  one_smul (a: α) : (1: R) • a = a

public class IsLawfulSMulZero (R α: Type*) [Zero α] [SMul R α] where
  smul_zero (r: R) : r • (0: α) = 0

public class IsLawfulZeroSMul (R α: Type*) [Zero R] [Zero α] [SMul R α] where
  zero_smul (a: α) : (0: R) • a = 0

public class IsLawfulMulSMul (R α: Type*) [Mul R] [SMul R α] where
  mul_smul (r s: R) (a: α) : (r * s) • a = r • s • a

public class IsLeftDistribSMul (R α: Type*) [Add R] [Add α] [SMul R α] where
  add_smul (r s: R) (a: α) : (r + s) • a = r • a + s • a

public class IsRightDistribSMul (R α: Type*) [Add α] [SMul R α] where
  smul_add (r: R) (a b: α) : r • (a + b) = r • a + r • b

public class IsSMulComm (R S α: Type*) [SMul R α] [SMul S α] where
  smul_comm (r: R) (s: S) (a: α) : r • s • a = s • r • a

public class IsScalarTower (R S α: Type*) [SMul R α] [SMul S α] [SMul R S] where
  smul_assoc (r: R) (s: S) (a: α) : (r • s) • a = r • s • a

public class IsCentralScalar (R α : Type*) [SMul R α] [SMul Rᵐᵒᵖ α]: Prop where
  rsmul_eq_lsmul : ∀(r : R) (a : α), a <• r = r •> a

export IsLawfulOneSMul (one_smul)
export IsLawfulSMulZero (smul_zero)
export IsLawfulZeroSMul (zero_smul)
export IsLawfulMulSMul (mul_smul)
export IsLeftDistribSMul (add_smul)
export IsRightDistribSMul (smul_add)
export IsSMulComm (smul_comm)
export IsScalarTower (smul_assoc)
export IsCentralScalar (rsmul_eq_lsmul)

public instance [Mul R] [IsComm R] [SMul R α]
  [IsLawfulMulSMul R α] : IsSMulComm R R α where
  smul_comm r s a := by rw [←mul_smul, ←mul_smul, mul_comm]

public instance [Mul R] [SMul R α] [IsLawfulMulSMul R α] : IsScalarTower R R α where
  smul_assoc r s a := by rw [←mul_smul]; rfl

end Property

section Basic

public instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsRightDistribSMul ℕ α where
  smul_add r a b := nsmul_add a b r
public instance [AddMonoidOps α] [IsAddMonoid α] : IsLeftDistribSMul ℕ α where
  add_smul r s a := add_nsmul a r s
public instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulZeroSMul ℕ α where
  zero_smul := zero_nsmul
public instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulSMulZero ℕ α where
  smul_zero := nsmul_zero
public instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulOneSMul ℕ α where
  one_smul := one_nsmul
public instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulMulSMul ℕ α where
  mul_smul r s a := mul_nsmul a r s
public instance
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α] [IsLawfulSMulZero R α] [IsRightDistribSMul R α]
  : IsSMulComm ℕ R α where
  smul_comm r s a := by
    induction r with
    | zero => rw [zero_smul, zero_smul, smul_zero]
    | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]
public instance
  [AddMonoidOps R] [IsAddMonoid R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α] [IsLawfulZeroSMul R α] [IsLeftDistribSMul R α]
  : IsScalarTower ℕ R α where
  smul_assoc r s a := by
    induction r with
    | zero => rw [zero_nsmul, zero_nsmul, zero_smul]
    | succ n ih => rw [succ_nsmul, succ_nsmul, add_smul, ih]
public instance [AddMonoidOps α] [IsAddMonoid α] : IsScalarTower ℕ ℕ α := inferInstance

public instance [Zero α] [Mul α] [IsLawfulZeroMul α] : IsLawfulSMulZero α α where
  smul_zero := mul_zero
public instance [Zero α] [Mul α] [IsLawfulZeroMul α] : IsLawfulZeroSMul α α where
  zero_smul := zero_mul
public instance [Mul α] [IsSemigroup α] : IsLawfulMulSMul α α where
  mul_smul := mul_assoc
public instance [One α] [Mul α] [IsLawfulOne α] : IsLawfulOneSMul α α where
  one_smul := one_mul

end Basic

namespace OfEquiv

variable (f: α ≃ β)

public instance [SMul S α] [Zero α] [IsLawfulSMulZero S α] : IsLawfulSMulZero S (OfEquiv f) where
  smul_zero r := by simp; rw [smul_zero]
public instance [SMul S α] [Zero S] [Zero α] [IsLawfulZeroSMul S α] : IsLawfulZeroSMul S (OfEquiv f) where
  zero_smul a := by
    induction a
    simp; rw [zero_smul]
public instance [SMul S α] [Add α] [IsRightDistribSMul S α] : IsRightDistribSMul S (OfEquiv f) where
  smul_add r a b := by
    induction a; induction b
    simp; rw [smul_add]
public instance [SMul S α] [Add S] [Add α] [IsLeftDistribSMul S α] : IsLeftDistribSMul S (OfEquiv f) where
  add_smul r s a := by
    induction a
    simp; rw [add_smul]
public instance [SMul S α] [One S] [IsLawfulOneSMul S α] : IsLawfulOneSMul S (OfEquiv f) where
  one_smul a := by induction a; simp; rw [one_smul]
public instance [SMul S α] [Mul S] [IsLawfulMulSMul S α] : IsLawfulMulSMul S (OfEquiv f) where
  mul_smul r s a := by induction a; simp; rw [mul_smul]

end OfEquiv

@[expose] public def smulHom {α β: Type*}
  [Zero α] [Add α]
  [Zero β] [Add β]
  [SMul α β]
  [IsLawfulZeroSMul α β]
  [IsLeftDistribSMul α β]
  (b: β) : α →+ β where
  toFun a := a • b
  map_zero := by rw [zero_smul]
  map_add _ _ := by rw [add_smul]
