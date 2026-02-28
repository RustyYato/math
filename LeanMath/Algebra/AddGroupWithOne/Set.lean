import LeanMath.Algebra.AddGroupWithOne.Defs
import LeanMath.Algebra.AddMonoidWithOne.Set
import LeanMath.Algebra.Group.Set

structure AddSubgroupWithOne (α: Type*) [Add α] [Neg α] [Zero α] [One α] extends AddSubgroup α, AddSubMonoidWithOne α where

instance [Add α] [Neg α] [Zero α] [One α] : SetLike (AddSubgroupWithOne α) α where
instance [Add α] [Neg α] [Zero α] [One α] : IsMemAdd (AddSubgroupWithOne α) α where
instance [Add α] [Neg α] [Zero α] [One α] : IsMemZero (AddSubgroupWithOne α) α where
instance [Add α] [Neg α] [Zero α] [One α] : IsMemOne (AddSubgroupWithOne α) α where

variable (s: S) [SetLike S α] [AddGroupWithOneOps α] [IsAddGroupWithOne α] [IsMemAdd S α] [IsMemNeg S α] [IsMemZero S α] [IsMemOne S α]

def mem_intCast (n: ℤ) : (n: α) ∈ s := by
  rw [intCast_eq_zsmul_one]
  apply mem_zsmul
  apply mem_one

instance : IntCast s where
  intCast n := {
    val := n
    property := mem_intCast s _
  }

instance : IsAddGroupWithOne s where
  intCast_ofNat _ := by
    apply Subtype.val_inj
    apply intCast_ofNat
  intCast_negSucc _ := by
    apply Subtype.val_inj
    apply intCast_negSucc
