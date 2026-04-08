import LeanMath.Algebra.Semigroup.Defs

class IsLawfulOneSMul (R α: Type*) [One R] [SMul R α] where
  protected one_smul (a: α) : (1: R) • a = a

class IsLawfulSMulZero (R α: Type*) [Zero α] [SMul R α] where
  protected smul_zero (r: R) : r • (0: α) = 0

class IsLawfulZeroSMul (R α: Type*) [Zero R] [Zero α] [SMul R α] where
  protected zero_smul (a: α) : (0: R) • a = 0

class IsLawfulMulSMul (R α: Type*) [Mul R] [SMul R α] where
  protected mul_smul (r s: R) (a: α) : (r * s) • a = r • s • a

class IsLeftDistribSMul (R α: Type*) [Add R] [Add α] [SMul R α] where
  protected add_smul (r s: R) (a: α) : (r + s) • a = r • a + s • a

class IsRightDistribSMul (R α: Type*) [Add α] [SMul R α] where
  protected smul_add (r: R) (a b: α) : r • (a + b) = r • a + r • b

class IsSMulComm (R S α: Type*) [SMul R α] [SMul S α] where
  protected smul_comm (r: R) (s: S) (a: α) : r • s • a = s • r • a

class IsScalarTower (R S α: Type*) [SMul R α] [SMul S α] [SMul R S] where
  protected smul_assoc (r: R) (s: S) (a: α) : (r • s) • a = r • s • a

class IsCentralScalar (R α : Type*) [SMul R α] [SMul Rᵐᵒᵖ α]: Prop where
  protected rsmul_eq_lsmul : ∀(r : R) (a : α), a <• r = r •> a

def one_smul [One R] [SMul R α] [IsLawfulOneSMul R α] (a: α) : (1: R) • a = a :=
  IsLawfulOneSMul.one_smul _
def smul_zero [Zero α] [SMul R α] [IsLawfulSMulZero R α] (r: R) : r • (0: α) = 0 :=
  IsLawfulSMulZero.smul_zero _
def zero_smul [Zero R] [Zero α] [SMul R α] [IsLawfulZeroSMul R α] (a: α) : (0: R) • a = 0 :=
  IsLawfulZeroSMul.zero_smul _
def mul_smul [Mul R] [SMul R α] [IsLawfulMulSMul R α] (r s: R) (a: α) : (r * s) • a = r • s • a :=
  IsLawfulMulSMul.mul_smul _ _ _
def add_smul [Add R] [Add α] [SMul R α] [IsLeftDistribSMul R α] (r s: R) (a: α) : (r + s) • a = r • a + s • a :=
  IsLeftDistribSMul.add_smul _ _ _
def smul_add [Add α] [SMul R α] [IsRightDistribSMul R α] (r: R) (a b: α) : r • (a + b) = r • a + r • b :=
  IsRightDistribSMul.smul_add _ _ _
def smul_comm [SMul R α] [SMul S α] [IsSMulComm R S α] (r: R) (s: S) (a: α) : r • s • a = s • r • a :=
  IsSMulComm.smul_comm _ _ _
def smul_assoc [SMul R α] [SMul S α] [SMul R S] [IsScalarTower R S α] (r: R) (s: S) (a: α) : (r • s) • a = r • s • a :=
  IsScalarTower.smul_assoc _ _ _
def rsmul_eq_lsmul [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] (r : R) (a : α) : a <• r = r •> a :=
  IsCentralScalar.rsmul_eq_lsmul _ _

instance [Mul R] [IsComm R] [SMul R α]
  [IsLawfulMulSMul R α] : IsSMulComm R R α where
  smul_comm r s a := by rw [←mul_smul, ←mul_smul, mul_comm]

instance [Mul R] [SMul R α] [IsLawfulMulSMul R α] : IsScalarTower R R α where
  smul_assoc r s a := by rw [←mul_smul]; rfl

structure LinearHom (R α β: Type*) [SMul R α] [SMul R β] [Add α] [Add β] extends SMulHom R α β, AddHom α β where

structure LinearEquiv (R α β: Type*) [SMul R α] [SMul R β] [Add α] [Add β] extends α ≃ β, LinearHom R α β where

notation:25 A " →ₗ[" R "] " B => LinearHom R A B
notation:25 A " ≃ₗ[" R "] " B => LinearEquiv R A B

variable
  [Add α] [Add β] [Add γ]
  [SMul R α] [SMul R β] [SMul R γ]

instance : FunLike (α →ₗ[R] β) α β where
instance : IsSMulHom (α →ₗ[R] β) R α β where
instance : IsAddHom (α →ₗ[R] β) α β where

instance : EquivLike (α ≃ₗ[R] β) α β where
instance : IsSMulHom (α ≃ₗ[R] β) R α β where
instance : IsAddHom (α ≃ₗ[R] β) α β where

def LinearHom.copy (f: α →ₗ[R] β) (g: α -> β) (h: ∀x, g x = f x) : α →ₗ[R] β where
  toFun := g
  map_smul := by
    intro r a
    rw [h, h, map_smul]
  map_add := by
    intro a b
    rw [h, h, h, map_add]

namespace OfEquiv

variable {R S α β: Type*} (f: α ≃ β)

protected scoped instance [One R] [SMul R β] [IsLawfulOneSMul R β] :  IsLawfulOneSMul R (OfEquiv f) where
  one_smul (a: (OfEquiv f)) : (1: R) • a = a := by
    dsimp; rw [one_smul, Equiv.coe_symm]

protected scoped instance [Zero β] [SMul R β] [IsLawfulSMulZero R β] :  IsLawfulSMulZero R (OfEquiv f) where
  smul_zero (r: R) : r • (0: (OfEquiv f)) = 0 := by
    dsimp; rw [Equiv.symm_coe, smul_zero]

protected scoped instance [Zero R] [Zero β] [SMul R β] [IsLawfulZeroSMul R β] :  IsLawfulZeroSMul R (OfEquiv f) where
  zero_smul (a: (OfEquiv f)) : (0: R) • a = 0 := by
    dsimp; rw [zero_smul]

protected scoped instance [Mul R] [SMul R β] [IsLawfulMulSMul R β] :  IsLawfulMulSMul R (OfEquiv f) where
  mul_smul (r s: R) (a: (OfEquiv f)) : (r * s) • a = r • s • a := by
    dsimp; rw [Equiv.symm_coe, mul_smul]

protected scoped instance [Add R] [Add β] [SMul R β] [IsLeftDistribSMul R β] :  IsLeftDistribSMul R (OfEquiv f) where
  add_smul (r s: R) (a: (OfEquiv f)) : (r + s) • a = r • a + s • a := by
    dsimp; rw [Equiv.symm_coe, Equiv.symm_coe, add_smul]

protected scoped instance [Add β] [SMul R β] [IsRightDistribSMul R β] :  IsRightDistribSMul R (OfEquiv f) where
  smul_add (r: R) (a b: (OfEquiv f)) : r • (a + b) = r • a + r • b := by
    dsimp; rw [Equiv.symm_coe, Equiv.symm_coe, Equiv.symm_coe, smul_add]

protected scoped instance [SMul R β] [SMul S β] [IsSMulComm R S β] :  IsSMulComm R S (OfEquiv f) where
  smul_comm (r: R) (s: S) (a: (OfEquiv f)) : r • s • a = s • r • a := by
    dsimp; rw [Equiv.symm_coe, Equiv.symm_coe, smul_comm]

protected scoped instance [SMul R β] [SMul S β] [SMul R S] [IsScalarTower R S β] : IsScalarTower R S (OfEquiv f) where
  smul_assoc (r: R) (s: S) (a: (OfEquiv f)) : (r • s) • a = r • s • a := by
    dsimp; rw [Equiv.symm_coe, smul_assoc]

protected scoped instance [SMul R β] [SMul Rᵐᵒᵖ β] [IsCentralScalar R β] :  IsCentralScalar R (OfEquiv f) where
  rsmul_eq_lsmul (r : R) (a : (OfEquiv f)) : a <• r = r •> a := by
    dsimp [lsmul_eq_smul, rsmul_eq_smul]; rw [←rsmul_eq_smul, ←lsmul_eq_smul, rsmul_eq_lsmul]

end OfEquiv
