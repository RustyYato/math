import LeanMath.Data.Real
import LeanMath.Data.RsqrtD.Ring

abbrev Complex := RsqrtD ℝ (-1: ℤ)

notation "ℂ" => Complex

namespace Complex

instance : RingOps ℂ := inferInstanceAs (RingOps (RsqrtD ℝ (-1: ℤ)))
instance : IsRing ℂ := inferInstanceAs (IsRing (RsqrtD ℝ (-1: ℤ)))

def ofReal : ℝ ↪+* ℂ := RsqrtD.of_real
instance : HasChar ℂ 0 := HasChar.of_ring_emb ofReal

end Complex
