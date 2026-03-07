import LeanMath.Data.LinearCombo.Defs
import LeanMath.Algebra.Module.Defs
import LeanMath.Logic.Nontrivial

namespace LinearCombo

instance
  {R S α: Type*}
  [AddMonoidOps R] [IsAddMonoid R] [IsAddComm R]
  [SemiringOps S] [IsSemiring S]
  [SMul S R] [IsModule S R]
  : IsModule S (LinearCombo R α) where
  zero_smul a := by
    induction a with
    | zero => rw [smul_zero]
    | ι => rw [smul_ι, zero_smul, map_zero]
    | add _ _ iha ihb => rw [smul_add, iha, ihb, add_zero]
  add_smul s₀ s₁ a := by
    induction a with
    | zero => simp [smul_zero, add_zero]
    | ι a r => simp [smul_ι, add_smul, map_add]
    | add a b iha ihb =>
      simp [smul_add, iha, ihb]
      ac_rfl

end LinearCombo
