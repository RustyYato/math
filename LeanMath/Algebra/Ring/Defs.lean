import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.AddGroupWithOne.Defs

class RingOps (α: Type*) extends SemiringOps α, AddGroupWithOneOps α where

instance (priority := 1100) [MonoidOps α] [AddGroupWithOneOps α] : RingOps α where

class IsRing (α: Type*) [RingOps α] : Prop extends IsSemiring α, IsAddGroupWithOne α where

section

variable [RingOps α] [IsRing α] [RingOps β] [IsRing β]
  [FunLike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

def neg_mul_left (a b: α) : -(a * b) = -a * b := by
  symm; apply eq_neg_of_add
  rw [←add_mul, neg_add_cancel, zero_mul]
def neg_mul_right (a b: α) : -(a * b) = a * -b := by
  symm; apply eq_neg_of_add
  rw [←mul_add, neg_add_cancel, mul_zero]

def zsmul_eq_intCast_mul (n: ℤ) (a: α) : n • a = n * a := by
  cases n with
  | ofNat n => rw [intCast_ofNat, ofNat_zsmul, nsmul_eq_natCast_mul]
  | negSucc n => rw [intCast_negSucc, negSucc_zsmul, nsmul_eq_natCast_mul, neg_mul_left]

def zsmul_eq_mul_intCast (n: ℤ) (a: α) : n • a = a * n := by
  cases n with
  | ofNat n => rw [intCast_ofNat, ofNat_zsmul, nsmul_eq_mul_natCast]
  | negSucc n => rw [intCast_negSucc, negSucc_zsmul, nsmul_eq_mul_natCast, neg_mul_right]

instance (n: ℤ) (a: α) : IsCommAt (n: α) a where
  mul_comm := by rw [←zsmul_eq_intCast_mul, ←zsmul_eq_mul_intCast]

instance (n: ℤ) (a: α) : IsCommAt a (n: α) := inferInstance

def intCast_mul (n m: ℤ) : (n * m: ℤ) = (n: α) * m := by
  rw [intCast_eq_zsmul_one, mul_zsmul, ←intCast_eq_zsmul_one,
    zsmul_eq_intCast_mul, mul_comm]

def intCastHom : ℤ →+* α := {
  intCastHom₀ with
  map_mul := intCast_mul
}

@[simp] def apply_intCastHom (n: ℤ) : intCastHom n = (n: α) := rfl

def intCast_npow (n: ℤ) (m: ℕ) : (n ^ m: ℤ) = (n: α) ^ m :=
  map_npow (f := intCastHom) _ _

variable [RelLike R α] [IsCon R] [IsAddCon R] [IsMulCon R] (r: R)

instance : IsRing (AlgQuot r) where

end

section

instance : IsRing ℤ where

end
