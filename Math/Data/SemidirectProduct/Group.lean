module

public import Math.Data.SemidirectProduct.Defs
public import Math.Algebra.Group.Defs.Hom
import Math.Algebra.Group.Defs.Lemmas

namespace Math

open scoped Automorphism

variable [GroupOps α] [GroupOps β] [IsGroup α] [IsGroup β]

public instance : Inv (SemidirectProduct α β f) where
  inv a := {
    fst := (f a.snd⁻¹) a.fst⁻¹
    snd := a.snd⁻¹
  }

public instance : Div (SemidirectProduct α β f) where
  div a b := a * b⁻¹

public instance : Pow (SemidirectProduct α β f) ℤ where
  pow a z := match z with
    | .ofNat z => a ^ z
    | .negSucc z => (a ^ (z + 1))⁻¹

@[simp] public theorem fst_inv (a: SemidirectProduct α β f) : a⁻¹.fst = (f a.snd⁻¹) a.fst⁻¹ := rfl
@[simp] public theorem snd_inv (a: SemidirectProduct α β f) : a⁻¹.snd = a.snd⁻¹ := rfl

public instance : IsGroup (SemidirectProduct α β f) where
  div_eq_mul_inv _ _ := rfl
  powz_ofNat _ _ := rfl
  powz_negSucc _ _ := rfl
  inv_mul_cancel a := by
    ext <;> dsimp
    rw [←map_mul, inv_mul_cancel, map_one]
    rw [inv_mul_cancel]
