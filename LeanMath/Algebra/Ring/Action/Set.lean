import LeanMath.Algebra.Module.Set
import LeanMath.Algebra.Ring.Action.Defs
import LeanMath.Algebra.Group.Set

variable (s: S) [SetLike S α] [SMul R α] [IsMemSMul S R α]
  [RingOps R] [IsRing R] [AddGroupOps α] [IsAddGroup α] [IsAddComm α] [IsModule R α]

@[implicit_reducible]
def IsMemNeg.ofIsMemSMul : IsMemNeg S α where
  mem_neg s a h := by
    rw [←one_smul (R:= R) a, neg_smul_left]
    apply mem_smul
    assumption

instance : IsMemNeg (Submodule R α) α := IsMemNeg.ofIsMemSMul (R := R)
