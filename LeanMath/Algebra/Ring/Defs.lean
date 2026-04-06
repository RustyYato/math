import LeanMath.Algebra.Semiring.Defs
import LeanMath.Algebra.AddGroupWithOne.Defs

class RingOps (α: Type*) extends SemiringOps α, AddGroupWithOneOps α where

instance (priority := 1100) [MonoidOps α] [AddGroupWithOneOps α] : RingOps α where

class IsRing (α: Type*) [RingOps α] : Prop extends IsSemiring α, IsAddGroupWithOne α where

section

variable [AddGroupOps α] [Mul α] [IsAddGroup α] [IsLawfulZeroMul α] [IsLeftDistrib α] [IsRightDistrib α]

def neg_mul_left (a b: α) : -(a * b) = -a * b := by
  symm; apply eq_neg_of_add
  rw [←add_mul, neg_add_cancel, zero_mul]
def neg_mul_right (a b: α) : -(a * b) = a * -b := by
  symm; apply eq_neg_of_add
  rw [←mul_add, neg_add_cancel, mul_zero]

instance (a b: α) [IsCommAt a b] : IsCommAt a (-b) where
  mul_comm := by rw [←neg_mul_left, ←neg_mul_right, mul_comm]

end

section

variable [RingOps α] [IsRing α] [RingOps β] [IsRing β]
  [FunLike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

def zsmul_eq_intCast_mul (n: ℤ) (a: α) : n • a = n * a := by
  cases n with
  | ofNat n => rw [intCast_ofNat, ofNat_zsmul, nsmul_eq_natCast_mul]
  | negSucc n => rw [intCast_negSucc, negSucc_zsmul, nsmul_eq_natCast_mul, neg_mul_left]

def zsmul_eq_mul_intCast (n: ℤ) (a: α) : n • a = a * n := by
  cases n with
  | ofNat n => rw [intCast_ofNat, ofNat_zsmul, nsmul_eq_mul_natCast]
  | negSucc n => rw [intCast_negSucc, negSucc_zsmul, nsmul_eq_mul_natCast, neg_mul_right]

def sub_mul (a b k: α) : (a - b) * k = a * k - b * k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_mul_left, add_mul]

def mul_sub (k a b: α) : k * (a - b) = k * a - k * b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_mul_right, mul_add]

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

instance : Subsingleton (ℤ →+* α) where
  allEq := by
    suffices ∀f: ℤ →+* α, f = intCastHom by
      intro a b; rw [this a, this b]
    intro f; apply DFunLike.ext; intro z
    show f (Int.cast z) = _
    rw [map_intCast]
    rfl

def intCast_npow (n: ℤ) (m: ℕ) : (n ^ m: ℤ) = (n: α) ^ m :=
  map_npow (f := intCastHom) _ _

def neg_sq (a: α) : (-a) ^ 2 = a ^ 2 := by
  rw [npow_two, npow_two, ←neg_mul_left, ←neg_mul_right, neg_neg]

def sub_sq (a b: α) [IsCommAt a b] : (a - b) ^ 2 = a ^ 2 - (2: ℕ) * (a * b) + b ^ 2 := by
  rw [sub_eq_add_neg, add_sq, neg_sq, ←neg_mul_right, ←neg_mul_right, sub_eq_add_neg]

variable [RelLike R α] [IsCon R] [IsAddCon R] [IsMulCon R] (r: R)

instance : IsRing (AlgQuot r) where

end

section

instance : IsRing ℤ where

end

instance [RingOps R] [IsRing R] : Neg (Units R) where
  neg a := {
    val := -a.val
    inv := -a.inv
    val_mul_inv := by rw [←neg_mul_left, ←neg_mul_right, neg_neg, a.val_mul_inv]
    inv_mul_val := by rw [←neg_mul_left, ←neg_mul_right, neg_neg, a.inv_mul_val]
  }

instance [RingOps R] [IsRing R] (r: R) [IsUnit r] : IsUnit (-r) where
  exists_eq_unit :=
    have ⟨u, h⟩ := IsUnit.exists_eq_unit (a := r)
    ⟨-u, by rw [h]; rfl⟩
