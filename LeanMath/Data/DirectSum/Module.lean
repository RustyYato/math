import LeanMath.Data.DirectSum.Defs
import LeanMath.Algebra.Module.Defs

namespace DirectSum

variable {α: Type*} {R: α -> Type*}
  {S: Type*} [SemiringOps S] [IsSemiring S] [∀a, SMul S (R a)]
  [∀a, AddMonoidOps (R a)] [∀a, IsAddMonoid (R a)] [∀a, IsAddComm (R a)]
  [∀a, IsModule S (R a)]

instance : IsModule S (⊕i, R i) where
  zero_smul a := by
    induction a with
    | zero => rw [smul_zero]
    | add a b iha ihb => rw [smul_add, iha, ihb, add_zero]
    | ι a r =>
      show (0: S) • ι a r = _
      rw [smul_ι, zero_smul, map_zero]
  add_smul r s a := by
    induction a with
    | zero => simp [smul_zero, add_zero]
    | add a b iha ihb => simp [smul_add, iha, ihb]; ac_rfl
    | ι a rₐ => simp [smul_ι, add_smul, map_add]

end DirectSum
