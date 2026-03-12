import LeanMath.Algebra.Semiring.Defs
import LeanMath.Data.Cardinal.Defs

namespace Cardinal

instance : IsAddComm Cardinal where
  add_comm a b := by
    cases a with | _ α =>
    cases b with | _ β =>
    apply sound
    apply Equiv.sum_comm

instance : IsComm Cardinal where
  mul_comm a b := by
    cases a with | _ α =>
    cases b with | _ β =>
    apply sound
    apply Equiv.prod_comm

instance : IsRightDistrib Cardinal where
  add_mul := by
    intro a b k
    cases a; cases b; cases k
    apply sound
    apply Equiv.sum_prod

instance : IsLawfulZeroMul Cardinal where
  zero_mul := by
    intro a; cases a; apply sound
    apply Equiv.empty
  mul_zero := by
    intro a; cases a; apply sound
    apply Equiv.empty

instance : IsLawfulNatCast Cardinal where
  natCast_zero := rfl
  natCast_one := rfl
  natCast_succ n := by
    apply sound
    apply Equiv.trans (Equiv.ulift _).symm
    apply flip Equiv.trans
    apply Equiv.sum_congr <;> apply Equiv.ulift
    refine {
      toFun x := if h:x.val < n then .inl ⟨_, h⟩ else .inr 0
      invFun
      | .inl x => x.castSucc
      | .inr _ => .last _
      leftInv := ?_
      rightInv := ?_
    }
    · intro x
      cases x
      simp; simp; apply Subsingleton.allEq
    · intro x
      cases x using Fin.lastCases
      simp
      simp

instance : IsMonoid Cardinal where
  mul_assoc a b c := by
    cases a; cases b; cases c
    apply sound
    apply Equiv.prod_assoc
  one_mul := by
    intro a; cases a
    apply sound;
    apply Equiv.unique_prod
  mul_one := by
    intro a; cases a
    rw [mul_comm]; apply sound;
    apply Equiv.unique_prod
  npow_zero a := by
    cases a; apply sound
    apply Equiv.unique
  npow_succ a n := by
    cases a; apply sound
    apply Equiv.trans
    apply Equiv.fun_congr
    apply (Equiv.ulift _).symm
    apply Equiv.id
    apply flip Equiv.trans
    apply Equiv.prod_congr
    apply Equiv.fun_congr (Equiv.ulift _)
    apply Equiv.id
    apply Equiv.id
    apply Equiv.fin_succ_func

instance : IsAddMonoid Cardinal where
  add_assoc a b c := by
    cases a; cases b; cases c
    apply sound
    apply Equiv.sum_assoc
  zero_add := by
    intro a; cases a
    apply sound;
    apply Equiv.empty_sum
  add_zero := by
    intro a; cases a
    rw [add_comm]; apply sound
    apply Equiv.empty_sum
  zero_nsmul := zero_mul
  succ_nsmul n a := by
    show _ * _ = _ * _ + _
    rw [natCast_succ, add_mul, one_mul]

instance : IsSemiring Cardinal where

end Cardinal
