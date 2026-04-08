import LeanMath.Algebra.Module.Defs
import LeanMath.Data.RsqrtD.Defs

namespace RsqrtD

instance
  [SemiringOps S] [IsSemiring S]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  [SMul S α] [IsModule S α] : IsModule S (RsqrtD α r) where
  one_smul := by intros; ext <;> (dsimp; rw [one_smul])
  mul_smul := by intros; ext <;> (dsimp; rw [mul_smul])
  smul_zero := by intros; ext <;> (dsimp; rw [smul_zero])
  smul_add := by intros; ext <;> (dsimp; rw [smul_add])
  zero_smul := by intros; ext <;> (dsimp; rw [zero_smul])
  add_smul := by intros; ext <;> (dsimp; rw [add_smul])

end RsqrtD
