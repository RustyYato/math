import LeanMath.Data.Encodable.Defs
import LeanMath.Data.FinEncodable.Pairing
import LeanMath.Data.Fintype.Defs

namespace FinEncodable

variable [DecidableEq α] [FinEncodable α]

scoped instance : Encodable α :=
  let eqv := FinEncodable.eqv α
  {
    decode i :=
      if h:i < FinEncodable.card α then
        .some (eqv ⟨i, h⟩)
      else
        .none
    encode i := eqv.symm i
    spec := by
      intro a
      rw [dif_pos]
      simp
      apply Fin.isLt
  }

end FinEncodable
