import LeanMath.Data.RsqrtD.Defs
import LeanMath.Algebra.Ring.Defs

namespace RsqrtD

variable {r: R}

instance [Neg α] : Neg (RsqrtD α r) where
  neg a := {
    real := -a.real
    imag := -a.imag
  }

instance [Sub α] : Sub (RsqrtD α r) where
  sub a b := {
    real := a.real - b.real
    imag := a.imag - b.imag
  }

@[simp] def neg_real [Neg α] (x: RsqrtD α r) : (-x).real = -x.real := rfl
@[simp] def neg_imag [Neg α] (x: RsqrtD α r) : (-x).imag = -x.imag := rfl

@[simp] def sub_real [Sub α] (x y: RsqrtD α r) : (x - y).real = x.real - y.real := rfl
@[simp] def sub_imag [Sub α] (x y: RsqrtD α r) : (x - y).imag = x.imag - y.imag := rfl

instance [AddGroupOps α] [IsAddGroup α] : IsAddGroup (RsqrtD α r) where
  sub_eq_add_neg _ _ := by ext <;> apply sub_eq_add_neg
  add_neg_cancel _ := by ext <;> apply add_neg_cancel
  ofNat_zsmul _ _ := by ext <;> apply ofNat_zsmul
  negSucc_zsmul _ _ := by ext <;> apply negSucc_zsmul

instance [RingOps α] [IsRing α] [RingOps R] [IsRing R] [AlgebraMap R α] [SMul R α] [IsAlgebra R α] : IsRing (RsqrtD α r) where
  intCast_ofNat _ := by ext; apply intCast_ofNat; rfl
  intCast_negSucc _ := by ext; apply intCast_negSucc; simp [neg_zero]

end RsqrtD
