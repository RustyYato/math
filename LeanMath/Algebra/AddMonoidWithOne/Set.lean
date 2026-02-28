import LeanMath.Algebra.AddMonoidWithOne.Defs
import LeanMath.Algebra.Monoid.Set

structure AddSubMonoidWithOne (α: Type*) [Add α] [Zero α] [One α] extends AddSubMonoid α, SubOne α where

instance [Add α] [Zero α] [One α] : SetLike (AddSubMonoidWithOne α) α where
instance [Add α] [Zero α] [One α] : IsMemAdd (AddSubMonoidWithOne α) α where
instance [Add α] [Zero α] [One α] : IsMemZero (AddSubMonoidWithOne α) α where
instance [Add α] [Zero α] [One α] : IsMemOne (AddSubMonoidWithOne α) α where

variable (s: S) [SetLike S α] [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] [IsMemAdd S α] [IsMemZero S α] [IsMemOne S α]

def mem_natCast (n: ℕ) : (n: α) ∈ s := by
  rw [natCast_eq_nsmul_one]
  apply mem_nsmul
  apply mem_one

instance : NatCast s where
  natCast n := {
    val := n
    property := mem_natCast s _
  }

instance : IsAddMonoidWithOne s where
  natCast_zero := by
    apply Subtype.val_inj
    apply natCast_zero
  natCast_one := by
    apply Subtype.val_inj
    apply natCast_one
  natCast_succ _ := by
    apply Subtype.val_inj
    apply natCast_succ
