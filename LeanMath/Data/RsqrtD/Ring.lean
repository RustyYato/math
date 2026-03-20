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

variable [RingOps α] [IsRing α] [RingOps R] [IsRing R] [AlgebraMap R α] [SMul R α] [IsAlgebra R α]

instance : RingOps (RsqrtD α r) := inferInstance

instance : IsRing (RsqrtD α r) where
  intCast_ofNat _ := by ext; apply intCast_ofNat; rfl
  intCast_negSucc _ := by ext; apply intCast_negSucc; simp [neg_zero]

def conj : RsqrtD α r ↪+* RsqrtD α r where
  toFun a := {
    real := a.real
    imag := -a.imag
  }
  inj {a b} h := by
    have ⟨h₀, h₁⟩ := mk.inj h
    rw [neg_inj] at h₁
    ext <;> assumption
  map_zero := by ext <;> simp [neg_zero]
  map_one := by congr; simp [neg_zero]
  map_add a b := by ext <;> simp [neg_add_rev, add_comm]
  map_mul a b := by
    ext <;> simp
    rw [←neg_mul_left, ←neg_mul_right, neg_neg]
    rw [←neg_mul_left, ←neg_mul_right, ←neg_add_rev, add_comm]

def apply_conj_real (a: RsqrtD α r) : (conj a).real = a.real := rfl
def apply_conj_imag (a: RsqrtD α r) : (conj a).imag = -a.imag := rfl

def conj_conj (a: RsqrtD α r) : conj (conj a) = a := by
  ext; rfl; apply neg_neg

end RsqrtD
