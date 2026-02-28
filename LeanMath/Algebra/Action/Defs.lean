import LeanMath.Algebra.Semigroup.Defs

class IsLawfulOneSMul (R α: Type*) [One R] [SMul R α] where
  protected one_smul (a: α) : (1: R) • a = a

class IsLawfulSMulZero (R α: Type*) [Zero α] [SMul R α] where
  protected smul_zero (r: R) : r • (0: α) = 0

class IsLawfulMulSMul (R α: Type*) [Mul R] [SMul R α] where
  protected mul_smul (r s: R) (a: α) : (r * s) • a = r • s • a

class IsLeftDistribSMul (R α: Type*) [Add R] [Add α] [SMul R α] where
  protected add_smul (r s: R) (a: α) : (r + s) • a = r • a + s • a

class IsRightDistribSMul (R α: Type*) [Add α] [SMul R α] where
  protected smul_add (r: R) (a b: α) : r • (a + b) = r • a + r • b

class IsSMulComm (R S α: Type*) [SMul R α] [SMul S α ] where
  protected smul_comm (r: R) (s: S) (a: α) : r • s • a = s • r • a

class IsScalarTower (R S α: Type*) [SMul R α] [SMul S α] [SMul R S] where
  protected smul_assoc (r: R) (s: S) (a: α) : (r • s) • a = r • s • a

class IsCentralScalar (R α : Type*) [SMul R α] [SMul Rᵐᵒᵖ α]: Prop where
  protected rsmul_eq_lsmul : ∀(r : R) (a : α), a <• r = r •> a

def one_smul [One R] [SMul R α] [IsLawfulOneSMul R α] (a: α) : (1: R) • a = a :=
  IsLawfulOneSMul.one_smul _
def smul_zero [Zero α] [SMul R α] [IsLawfulSMulZero R α] (r: R) : r • (0: α) = 0 :=
  IsLawfulSMulZero.smul_zero _
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

instance [Mul R] [IsComm R] [SMul R α] : IsCentralScalar R α where
  rsmul_eq_lsmul _ _ := rfl
