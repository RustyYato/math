import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.Algebra.Defs

-- α√r = a + √r • b
@[ext]
structure RsqrtD {R: Type*} (α: Type*) (r: R) where
  real: α
  imag: α

namespace RsqrtD

variable {r: R}

instance [Zero α] : Zero (RsqrtD α r) where
  zero := {
    real := 0
    imag := 0
  }

instance [One α] [Zero α] : One (RsqrtD α r) where
  one := {
    real := 1
    imag := 0
  }

instance [NatCast α] [Zero α] : NatCast (RsqrtD α r) where
  natCast n := {
    real := n
    imag := 0
  }

instance [IntCast α] [Zero α] : IntCast (RsqrtD α r) where
  intCast n := {
    real := n
    imag := 0
  }

instance [Add α] : Add (RsqrtD α r) where
  add x y := {
    real := x.real + y.real
    imag := x.imag + y.imag
  }

instance [SMul S α] : SMul S (RsqrtD α r) where
  smul s x := {
    real := s • x.real
    imag := s • x.imag
  }

@[simp] def zero_real [Zero α] : (0: RsqrtD α r).real = 0 := rfl
@[simp] def zero_imag [Zero α] : (0: RsqrtD α r).imag = 0 := rfl

@[simp] def one_real [One α] [Zero α] : (1: RsqrtD α r).real = 1 := rfl
@[simp] def one_imag [One α] [Zero α] : (1: RsqrtD α r).imag = 0 := rfl

@[simp] def natCast_real [NatCast α] [Zero α] (n: ℕ) : (n: RsqrtD α r).real = n := rfl
@[simp] def natCast_imag [NatCast α] [Zero α] (n: ℕ) : (n: RsqrtD α r).imag = 0 := rfl

@[simp] def intCast_real [IntCast α] [Zero α] (n: ℤ) : (n: RsqrtD α r).real = n := rfl
@[simp] def intCast_imag [IntCast α] [Zero α] (n: ℤ) : (n: RsqrtD α r).imag = 0 := rfl

@[simp] def add_real [Add α] (x y: RsqrtD α r) : (x + y).real = x.real + y.real := rfl
@[simp] def add_imag [Add α] (x y: RsqrtD α r) : (x + y).imag = x.imag + y.imag := rfl

@[simp] def smul_real [SMul S α] (s: S) (x: RsqrtD α r) : (s • x).real = s • x.real := rfl
@[simp] def smul_imag [SMul S α] (s: S) (x: RsqrtD α r) : (s • x).imag = s • x.imag := rfl

instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (RsqrtD α r) where
  add_assoc _ _ _ := by ext <;> apply add_assoc
  zero_add _ := by ext <;> apply zero_add
  add_zero _ := by ext <;> apply add_zero
  zero_nsmul _ := by ext <;> apply zero_nsmul
  succ_nsmul _ _ := by ext <;> apply succ_nsmul

instance [Mul α] [Add α] [SMul R α] : Mul (RsqrtD α r) where
  mul x y := {
    real := x.real * y.real + r • (x.imag * y.imag)
    imag := x.real * y.imag + x.imag * y.real
  }

@[simp] def mul_real [Mul α] [Add α] [SMul R α] (x y: RsqrtD α r) : (x * y).real = x.real * y.real + r • (x.imag * y.imag) := rfl
@[simp] def mul_imag [Mul α] [Add α] [SMul R α] (x y: RsqrtD α r) : (x * y).imag = x.real * y.imag + x.imag * y.real := rfl

instance [Zero α] [One α] [Mul α] [Add α] [SMul R α] : Pow (RsqrtD α r) ℕ := defaultPowN

instance  [Add α] [IsAddComm α] : IsAddComm (RsqrtD α r) where
  add_comm _ _ := by ext <;> apply add_comm

instance [Zero α] [One α] [Mul α] [Add α] [SMul R α] [IsAddComm α] [IsComm α] : IsComm (RsqrtD α r) where
  mul_comm a b := by
    ext <;> dsimp
    congr 1 <;> rw [mul_comm]
    rw [add_comm]
    congr 1 <;> rw [mul_comm]

instance [SemiringOps α] [IsSemiring α] [SemiringOps R] [IsSemiring R] [AlgebraMap R α] [SMul R α] [IsAlgebra R α] : IsSemiring (RsqrtD α r) where
  mul_assoc a b c := by
    ext
    all_goals simp [mul_add, add_mul, mul_assoc, smul_def]
    all_goals repeat first|rw [←mul_comm _ (algebraMap R r)]|rw [←mul_assoc]
    ac_rfl
    ac_rfl
  one_mul a := by ext <;> simp [one_mul, zero_mul, smul_zero, add_zero]
  mul_one a := by ext <;> simp [mul_one, mul_zero, smul_zero, zero_add, add_zero]
  natCast_zero := by ext; apply natCast_zero; rfl
  natCast_one := by ext; apply natCast_one; rfl
  natCast_succ _ := by ext; apply natCast_succ; symm; apply add_zero
  zero_mul a := by ext <;> simp [zero_mul, smul_zero, add_zero]
  mul_zero a := by ext <;> simp [mul_zero, smul_zero, add_zero]
  add_mul a b k := by
    ext <;> simp [add_mul, smul_add]
    ac_rfl
    ac_rfl
  mul_add k a b := by
    ext <;> simp [mul_add, smul_add]
    ac_rfl
    ac_rfl

def of_real [Zero α] [One α] [Mul α] [Add α] [SMul R α]
  [IsLawfulZeroAdd α] [IsLawfulZeroMul α] [IsLawfulSMulZero R α]
  : α ↪+* RsqrtD α r where
  toFun a := {
    real := a
    imag := 0
  }
  inj := by
    intro a b h
    exact (RsqrtD.mk.inj h).left
  map_zero := rfl
  map_one := rfl
  map_add _ _ := by ext; rfl; symm; apply add_zero
  map_mul a b := by ext <;> simp [add_zero, mul_zero, smul_zero, zero_mul]

end RsqrtD
