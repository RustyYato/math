import LeanMath.Algebra.AddMonoidWithOne.Defs

class SemiringOps (α: Type*) extends AddMonoidWithOneOps α, MonoidOps α where

instance (priority := 1100) [AddMonoidWithOneOps α] [MonoidOps α] : SemiringOps α where

class IsLeftDistrib (α: Type*) [Mul α] [Add α] : Prop where
  protected mul_add (k a b: α) : k * (a + b) = k * a + k * b

class IsRightDistrib (α: Type*) [Mul α] [Add α] : Prop where
  protected add_mul (a b k: α) : (a + b) * k = a * k + b * k

def mul_add [Mul α] [Add α] [IsLeftDistrib α] (k a b: α) : k * (a + b) = k * a + k * b :=
  IsLeftDistrib.mul_add _ _ _

def add_mul [Mul α] [Add α] [IsRightDistrib α] (a b k: α) : (a + b) * k = a * k + b * k :=
  IsRightDistrib.add_mul _ _ _

instance (priority := 100) [Mul α] [Add α] [IsComm α] [IsLeftDistrib α]
  : IsRightDistrib α where
  add_mul a b k := by
    repeat rw [mul_comm _ k]
    rw [mul_add]
instance (priority := 100) [Mul α] [Add α] [IsComm α] [IsRightDistrib α]
  : IsLeftDistrib α where
  mul_add k a b := by
    repeat rw [mul_comm k]
    rw [add_mul]

class IsSemiring (α: Type*) [SemiringOps α] : Prop extends IsAddMonoidWithOne α, IsMonoid α, IsLeftDistrib α, IsRightDistrib α, IsLawfulZeroMul α where

section

structure RingHom (α β: Type*)
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] [One α] [One β] extends Hom α β, MulHom α β, AddHom α β, α →₀ β, α →₁ β, α →* β, α →+ β, α →+₁ β where

infixr:80 " →+* " => RingHom

variable
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] [One α] [One β]

instance (priority := 10000) : FunLike (α →+* β) α β where
instance (priority := 10000) : IsZeroHom (α →+* β) α β where
instance (priority := 10000) : IsAddHom (α →+* β) α β where
instance (priority := 10000) : IsOneHom (α →+* β) α β where
instance (priority := 10000) : IsMulHom (α →+* β) α β where

end

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

def natCastHom : ℕ →+* α := {
  natCastHom₀ with
  map_mul := natCast_mul
}

@[simp] def apply_natCastHom (n: ℕ) : natCastHom n = (n: α) := rfl

def natCast_npow (n m: ℕ) : (n ^ m: ℕ) = (n: α) ^ m :=
  map_npow (f := natCastHom) _ _

end

section

instance : IsLeftDistrib ℕ where
  mul_add := Nat.mul_add
instance : IsRightDistrib ℕ := inferInstance
instance : IsSemiring ℕ where

instance : IsLeftDistrib ℤ where
  mul_add := Int.mul_add
instance : IsRightDistrib ℤ := inferInstance
instance : IsSemiring ℤ where

end
