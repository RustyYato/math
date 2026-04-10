import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Semifield.Defs

class FieldOps (α: Type*) extends SemifieldOps α, RingOps α where

instance (priority := 1200) [ha: GroupWithZeroOps α] [hb: AddGroupWithOneOps α] : FieldOps α := {
    ha, hb with
}

class IsDivisionRing (α: Type*) [FieldOps α] : Prop extends IsDivisionSemiring α, IsRing α where
class IsField (α: Type*) [FieldOps α] : Prop extends IsDivisionRing α, IsSemifield α where

section

variable [FieldOps α] [IsDivisionRing α]

def neg_div?_left (a b: α) (hb: b ≠ 0) : -(a /? b) = -a /? b := by
  rw [div?_eq_mul_inv?, div?_eq_mul_inv?, neg_mul_left]

def div?_sub_div? (a b c d: α) [IsCommAt b d] (hb: b ≠ 0) (hd: d ≠ 0) : a /? b - c /? d = (a * d - c * b) /? (b * d) := by
  rw [sub_eq_add_neg, neg_div?_left, sub_eq_add_neg, neg_mul_left, div?_add_div?]

def intCast_div?_intCast (n m: ℤ) (h: m ∣ n) (hm: (m: α) ≠ 0 := by invert_tactic) : (n / m: ℤ) = (n: α) /? (m: α) := by
  apply of_mul_right₀
  assumption
  rw [div?_mul_cancel, ←intCast_mul, Int.ediv_mul_cancel]
  assumption

def sub_div? (a b k: α) (hk: k ≠ 0) : (a - b) /? k = a /? k - b /? k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_div?, neg_div?_left]

end

variable {R D: Type*} [FunLike F D R] [FieldOps D] [RingOps R] [IsRing R] [IsDivisionRing D]
  [IsZeroHom F D R] [IsOneHom F D R] [IsAddHom F D R] [IsMulHom F D R]
  [IsZeroNeOne R] [ExcludedMiddleEq D]

instance : EmbeddingLike F D R where
  coeEmbedding f := {
    toFun := f
    inj {a b} h := by
      replace h : f a - f b = 0 := by rw [h, sub_self]
      rw [←map_sub] at h
      rw [←neg_neg b]; apply eq_neg_of_add
      rw [←sub_eq_add_neg]
      revert h; generalize a - b = x
      clear a b; intro h
      apply LEM.byContradiction
      intro g
      have : f (x * x⁻¹?) = 1 := by rw [mul_inv?_cancel, map_one]
      rw [map_mul, h, zero_mul] at this
      exact zero_ne_one _ this
  }

def RingEmbedding.ofFieldHom (f: F) : D ↪+* R where
  toFun := f
  inj := inj f
  map_zero := map_zero f
  map_one := map_one f
  map_add := map_add f
  map_mul := map_mul f

namespace OfEquiv

variable (f: α ≃ β)

protected scoped instance [ops: FieldOps β] : FieldOps (OfEquiv f) where

protected scoped instance [FieldOps β] [IsDivisionRing β] : IsDivisionRing (OfEquiv f) where

protected scoped instance [FieldOps β] [IsField β] : IsField (OfEquiv f) where

end OfEquiv
