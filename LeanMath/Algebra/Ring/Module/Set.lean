import LeanMath.Algebra.Module.Set
import LeanMath.Algebra.Group.Action.Defs
import LeanMath.Algebra.Ring.Set
import LeanMath.Algebra.Ring.Module.Defs

variable (s: S) [SetLike S α] [SMul R α] [IsMemSMul S R α]
variable [RingOps R] [IsRing R] [AddGroupOps α] [IsAddGroup α] [IsAddComm α] [IsMemZero S α] [IsMemAdd S α]
  [IsModule R α]

instance : IsMemNeg (Submodule R α) α where
  mem_neg := by
    intro S a ha
    rw [←one_smul (R := R) a, ←neg_one_zsmul, ←smul_assoc, ]
    apply mem_smul
    assumption
