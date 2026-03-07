import LeanMath.Algebra.Module.Defs
import LeanMath.Algebra.Monoid.Action.Set
import LeanMath.Algebra.Semiring.Set

variable (s: S) [SetLike S α] [SMul R α] [IsMemSMul S R α]
variable [SemiringOps R] [IsSemiring R] [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] [IsMemZero S α] [IsMemAdd S α]

instance [IsModule R α] : IsModule R s where
  add_smul _ _ _ := by
    apply Subtype.val_inj
    apply add_smul
  zero_smul _ := by
    apply Subtype.val_inj
    apply zero_smul
