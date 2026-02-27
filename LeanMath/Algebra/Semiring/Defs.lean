import LeanMath.Algebra.AddMonoidWithOne.Defs

class SemiringOps (α: Type*) extends AddMonoidWithOneOps α, MonoidOps α where

class IsLeftDistrib (α: Type*) [Mul α] [Add α] : Prop where
  protected mul_add (k a b: α) : k * (a + b) = k * a + k * b

class IsRightDistrib (α: Type*) [Mul α] [Add α] : Prop where
  protected add_mul (a b k: α) : (a + b) * k = a * k + b * k

def mul_add [Mul α] [Add α] [IsLeftDistrib α] (k a b: α) : k * (a + b) = k * a + k * b :=
  IsLeftDistrib.mul_add _ _ _

def add_mul [Mul α] [Add α] [IsRightDistrib α] (a b k: α) : (a + b) * k = a * k + b * k :=
  IsRightDistrib.add_mul _ _ _

instance (priority := 1100) [Mul α] [Add α] [IsComm α] [IsLeftDistrib α]
  : IsRightDistrib α where
  add_mul a b k := by
    repeat rw [mul_comm _ k]
    rw [mul_add]
instance (priority := 1100) [Mul α] [Add α] [IsComm α] [IsRightDistrib α]
  : IsLeftDistrib α where
  mul_add k a b := by
    repeat rw [mul_comm k]
    rw [add_mul]

class IsSemiring (α: Type*) [SemiringOps α] : Prop extends IsAddMonoidWithOne α, IsMonoid α, IsLeftDistrib α, IsRightDistrib α, IsLawfulZeroMul α where

section

variable [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [FunLike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

def nsmul_eq_natCast_mul (n: ℕ) (a: α) : n • a = n * a := by
  induction n with
  | zero => rw [natCast_zero, zero_mul, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, add_mul, one_mul, ih]

def nsmul_eq_mul_natCast (n: ℕ) (a: α) : n • a = a * n := by
  induction n with
  | zero => rw [natCast_zero, mul_zero, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, mul_add, mul_one, ih]

instance (n: ℕ) (a: α) : IsCommAt (n: α) a where
  mul_comm := by rw [←nsmul_eq_mul_natCast, ←nsmul_eq_natCast_mul]

instance (n: ℕ) (a: α) : IsCommAt a (n: α) := inferInstance

def natCast_mul (n m: ℕ) : (n * m: ℕ) = (n: α) * m := by
  rw [natCast_eq_nsmul_one, mul_nsmul, ←natCast_eq_nsmul_one,
    nsmul_eq_natCast_mul, mul_comm]

end
