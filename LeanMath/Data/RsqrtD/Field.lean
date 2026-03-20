import LeanMath.Data.RsqrtD.Ring
import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Group.Action.Defs

namespace RsqrtD

variable {r: R}

class NoSolution (α: Type*) [SemiringOps R] [SemiringOps α] [AlgebraMap R α] (r: R) where
  protected sq_ne_r (a: α) : a ^ 2 ≠ algebraMap R r

variable [FieldOps α] [IsField α] [RingOps R] [IsRing R] [AlgebraMap R α] [SMul R α] [IsAlgebra R α]

def eq_zero_of_mul_conj_eq_zero [NoSolution α r] (a: RsqrtD α r) : a * conj a = 0 -> a = 0 := by
  intro h
  replace ⟨h, g⟩ := mk.inj h
  simp [←neg_mul_right] at h g
  rw [add_comm, ←sub_eq_add_neg, ←sub_eq_zero] at g
  rw [←neg_smul_right, ←sub_eq_add_neg, ←sub_eq_zero,
    smul_def] at h

  sorry

instance : CheckedInv? (RsqrtD α r) where
  checked_inv a h :=
    let d := a * conj a
    {
      real := sorry
      imag := sorry
    }
-- instance : IsGroupWithZero (RsqrtD α r) where
--   mul_inv?_cancel := by sorry


end RsqrtD
