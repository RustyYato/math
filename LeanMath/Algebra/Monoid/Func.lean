import LeanMath.Algebra.Monoid.Defs
import LeanMath.Algebra.Semigroup.Func

variable {ι: Type*} {A: ι -> Type*} {α: Type*}

instance [∀i, Zero (A i)] : Zero (∀i, A i) where
  zero _ := 0

instance [∀i, One (A i)] : One (∀i, A i) where
  one _ := 1

instance [∀i, SMul R (A i)] : SMul R (∀i, A i) where
  smul r a i := r • a i

instance [∀i, Pow (A i) R] : Pow (∀i, A i) R where
  pow a r i := a i ^ r

instance [∀i, One (A i)] : One (∀i, A i) where
  one _ := 1

instance [Zero α] : Zero (ι -> α) := inferInstance
instance [One α] : One (ι -> α) := inferInstance
instance [SMul R α] : SMul R (ι -> α) := inferInstance
instance [Pow α R] : Pow (ι -> α) R := inferInstance
instance [One α] : One (ι -> α) := inferInstance

instance [∀i, One (A i)] : IsOneHom (Apply A i) (∀i, A i) (A i) where
  map_one _ := rfl
instance [∀i, Zero (A i)] : IsZeroHom (Apply A i) (∀i, A i) (A i) where
  map_zero _ := rfl
instance [∀i, SMul R (A i)] : IsSMulHom (Apply A i) R (∀i, A i) (A i) where
  map_smul _ _ _ := rfl

@[simp] def Function.apply_one [∀i, One (A i)] (i: ι) : (1: ∀i, A i) i = 1 := rfl
@[simp] def Function.apply_zero [∀i, Zero (A i)] (i: ι) : (0: ∀i, A i) i = 0 := rfl
@[simp] def Function.apply_smul [∀i, SMul R (A i)] (r: R) (a: ∀i, A i) (i: ι) : (r • a) i = r • a i := rfl
@[simp] def Function.apply_pow [∀i, Pow (A i) R] (a: ∀i, A i) (r: R) (i: ι) : (a ^ r) i = a i ^ r := rfl

instance [∀i, Mul (A i)] [∀i, One (A i)] [∀i, IsLawfulOneMul (A i)] : IsLawfulOneMul (∀i, A i) where
  one_mul a := by ext i; apply one_mul
  mul_one a := by ext i; apply mul_one
instance [∀i, Mul (A i)] [∀i, Zero (A i)] [∀i, IsLawfulZeroMul (A i)] : IsLawfulZeroMul (∀i, A i) where
  zero_mul a := by ext i; apply zero_mul
  mul_zero a := by ext i; apply mul_zero
instance [∀i, Add (A i)] [∀i, Zero (A i)] [∀i, IsLawfulZeroAdd (A i)] : IsLawfulZeroAdd (∀i, A i) where
  zero_add a := by ext i; apply zero_add
  add_zero a := by ext i; apply add_zero
instance [∀i, MonoidOps (A i)] [∀i, IsLawfulPowN (A i)] : IsLawfulPowN (∀i, A i) where
  npow_zero a := by ext i; apply npow_zero
  npow_succ a n := by ext i; apply npow_succ
instance [∀i, AddMonoidOps (A i)] [∀i, IsLawfulNSMul (A i)] : IsLawfulNSMul (∀i, A i) where
  zero_nsmul a := by ext i; apply zero_nsmul
  succ_nsmul n a := by ext i; apply succ_nsmul
instance [∀i, MonoidOps (A i)] [∀i, IsMonoid (A i)] : IsMonoid (∀i, A i) where
instance [∀i, AddMonoidOps (A i)] [∀i, IsAddMonoid (A i)] : IsAddMonoid (∀i, A i) where

instance [Mul α] [One α] [IsLawfulOneMul α] : IsLawfulOneMul (ι -> α) := inferInstance
instance [Mul α] [Zero α] [IsLawfulZeroMul α] : IsLawfulZeroMul (ι -> α) := inferInstance
instance [Add α] [Zero α] [IsLawfulZeroAdd α] : IsLawfulZeroAdd (ι -> α) := inferInstance
instance [MonoidOps α] [IsLawfulPowN α] : IsLawfulPowN (ι -> α) := inferInstance
instance [AddMonoidOps α] [IsLawfulNSMul α] : IsLawfulNSMul (ι -> α) := inferInstance
instance [MonoidOps α] [IsMonoid α] : IsMonoid (ι -> α) := inferInstance
instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (ι -> α) := inferInstance
