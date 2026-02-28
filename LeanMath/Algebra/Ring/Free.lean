import LeanMath.Algebra.Semiring.Free
import LeanMath.Algebra.Ring.Defs

namespace FreeAlgebra

variable [RingOps R] [IsRing R]

instance : Neg (FreeAlgebra R α) where
  neg a := algebraMap R (-1) * a

instance : Sub (FreeAlgebra R α) where
  sub a b := a + -b

instance : SMul ℤ (FreeAlgebra R α) := defaultSMulZ

instance : IntCast (FreeAlgebra R α) := defaultIntCast _

instance : IsRing (FreeAlgebra R α) where
  sub_eq_add_neg _ _ := rfl
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul _ _ := rfl
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
  add_neg_cancel a := by
    show a + algebraMap R (-1) * a = 0
    rw (occs := [1]) [←one_mul a]
    rw [←map_one (algebraMap R), ←add_mul,
      ←map_add, add_neg_cancel, map_zero, zero_mul]

end FreeAlgebra
