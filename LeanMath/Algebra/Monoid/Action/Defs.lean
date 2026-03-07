import LeanMath.Algebra.Action.Defs
import LeanMath.Algebra.Monoid.Defs

class IsMonoidAction (R α: Type*) [MonoidOps R] [IsMonoid R] [SMul R α]
  : Prop extends IsLawfulOneSMul R α, IsLawfulMulSMul R α where

class IsDistributiveAction (R α: Type*)
  [MonoidOps R] [IsMonoid R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α]
  : Prop extends IsMonoidAction R α, IsLawfulSMulZero R α, IsRightDistribSMul R α where

instance [AddMonoidOps α] [IsAddMonoid α] : IsMonoidAction ℕ α where
  one_smul a := by rw [one_nsmul]
  mul_smul r s a := by rw [mul_comm, mul_nsmul]

instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulSMulZero ℕ α where
  smul_zero r := by rw [nsmul_zero]

instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsDistributiveAction ℕ α where
  smul_add r a b := by rw [nsmul_add]

instance [AddMonoidOps α] [IsAddMonoid α] : IsLeftDistribSMul ℕ α where
  add_smul r s a := by rw [add_nsmul]

instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulZeroSMul ℕ α where
  zero_smul a := by rw [zero_nsmul]

instance [AddMonoidOps α] [IsAddMonoid α] : IsScalarTower ℕ ℕ α where
  smul_assoc r s a := by
    show (r * s) • a = _
    rw [mul_comm, mul_nsmul]

instance [SMul R α] [AddMonoidOps α] [IsAddMonoid α] [IsRightDistribSMul R α] [IsLawfulSMulZero R α] : IsSMulComm ℕ R α where
  smul_comm r s a := by
    induction r with
    | zero => rw [zero_smul, zero_smul, smul_zero]
    | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

def smulHom (R: Type*) {α: Type*}
  [Add α] [Zero α] [SMul R α]
  [IsLawfulSMulZero R α]
  [IsRightDistribSMul R α] (r: R) : α →+ α where
  toFun a := r • a
  map_zero := smul_zero _
  map_add := smul_add _

def smulHom' (R: Type*)
  [Zero R] [Add R] [Zero α] [Add α] [SMul R α]
  [IsLawfulZeroSMul R α]
  [IsLeftDistribSMul R α] (a: α) : R →+ α where
  toFun r := r • a
  map_zero := zero_smul _
  map_add _ _ := add_smul _ _ _

section

instance
  [Zero α] [Add α]
  [SMul R β] [MonoidOps R] [IsMonoid R]
  [AddMonoidOps β] [IsAddMonoid β]
  [IsLawfulSMulZero R β]
  [IsRightDistribSMul R β] : SMul R (α →+ β) where
  smul r f := {
    toFun a := r • f a
    map_zero := by rw [map_zero, smul_zero]
    map_add a b := by rw [map_add, smul_add]
  }

instance
  [Zero α] [Add α]
  [AddMonoidOps β] [IsAddMonoid β] [IsAddComm β] : IsAddMonoid (α →+ β) where
  zero_nsmul _ := by
    apply DFunLike.ext; intro
    apply zero_nsmul
  succ_nsmul _ _ := by
    apply DFunLike.ext; intro
    apply succ_nsmul

end

section

variable
  [Zero α] [Zero β] [Zero γ]
  [Add α] [Add β] [Add γ]
  [SMul R α] [SMul R β] [SMul R γ]

instance [Zero R] [IsLawfulZeroSMul R α] [IsLawfulZeroSMul R β] : IsZeroHom (α →ₗ[R] β) α β where
  map_zero := by
    intro f
    rw [←zero_smul (R := R) (0: α), map_smul, zero_smul]

instance [Zero R] [IsLawfulZeroSMul R α] [IsLawfulZeroSMul R β] : IsZeroHom (α ≃ₗ[R] β) α β where
  map_zero := by
    intro f
    rw [←zero_smul (R := R) (0: α), map_smul, zero_smul]

instance [IsLawfulSMulZero R β] [IsLawfulZeroAdd β] : Zero (α →ₗ[R] β) where
  zero := {
    toFun _ := 0
    map_smul := by
      intro r' a
      rw [smul_zero]
    map_add a b := by rw [add_zero]
  }

instance [SMul S β] [IsSMulComm S R β] [IsRightDistribSMul S β] : SMul S (α →ₗ[R] β) where
  smul s f := {
    toFun x := s • f x
    map_smul := by
      intro r a
      rw [map_smul, smul_comm]
    map_add a b := by
      rw [map_add, smul_add]
  }

instance [IsRightDistribSMul R β] [IsAddComm β] [IsAddSemigroup β] : Add (α →ₗ[R] β) where
  add f g := {
    toFun x := f x + g x
    map_smul := by
      intro r' a
      rw [map_smul, map_smul, smul_add]
    map_add a b := by
      rw [map_add, map_add]
      ac_rfl
  }

end

instance [SMul R α] [Add α] [SMul R β] [IsSMulComm R R β] [Add β] [IsRightDistribSMul R β] [MonoidOps R] [IsMonoid R] [IsMonoidAction R β]: IsMonoidAction R (α →ₗ[R] β) where
  one_smul f := by
    apply DFunLike.ext; intro x
    apply one_smul
  mul_smul _ _ _ := by
    apply DFunLike.ext; intro x
    apply mul_smul

variable [SMul R α] [Add α] [SMul R β] [AddMonoidOps β] [IsAddComm β] [IsAddMonoid β] [IsLawfulSMulZero R β] [IsSMulComm R R β] [IsRightDistribSMul R β]

instance : IsAddComm (α →ₗ[R] β) where
  add_comm _ _ := by
    apply DFunLike.ext; intro x
    apply add_comm

instance : IsAddMonoid (α →ₗ[R] β) where
  add_assoc _ _ _ := by
    apply DFunLike.ext; intro x
    apply add_assoc
  zero_add _ := by
    apply DFunLike.ext; intro x
    apply zero_add
  add_zero _ := by
    apply DFunLike.ext; intro x
    apply add_zero
  zero_nsmul _ := by
    apply DFunLike.ext; intro x
    apply zero_nsmul
  succ_nsmul _ _ := by
    apply DFunLike.ext; intro x
    apply succ_nsmul

instance [MonoidOps R] [IsMonoid R] [IsDistributiveAction R β] : IsDistributiveAction R (α →ₗ[R] β) where
  smul_zero _ := by
    apply DFunLike.ext; intro x
    apply smul_zero
  smul_add _ _ _ := by
    apply DFunLike.ext; intro x
    apply smul_add
