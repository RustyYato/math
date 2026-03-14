import LeanMath.Algebra.Ring.Defs
import LeanMath.Algebra.Semifield.Defs

class FieldOps (α: Type*) extends SemifieldOps α, RingOps α where

class IsDivisionRing (α: Type*) [FieldOps α] : Prop extends IsDivisionSemiring α, IsRing α where
class IsField (α: Type*) [FieldOps α] : Prop extends IsDivisionRing α, IsSemifield α where

variable {R D: Type*} [FunLike F D R] [FieldOps D] [RingOps R] [IsRing R] [IsDivisionRing D]
  [IsZeroHom F D R] [IsOneHom F D R] [IsAddHom F D R] [IsMulHom F D R]
  [Nontrivial R] [DecidableEq D] [DecidableEq R]

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
      apply Decidable.byContradiction
      intro g
      have : f (x * x⁻¹?) = 1 := by rw [mul_inv?_cancel, map_one]
      rw [map_mul, h, zero_mul] at this
      contradiction
  }
