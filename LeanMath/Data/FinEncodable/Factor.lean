import LeanMath.Data.Fintype.Defs

namespace FinEncodable

private def is_inr : α ⊕' β -> Bool
| .inl _ => false
| .inr _ => true

def factorBijOrEquiv {ι: Sort*} {α: ι -> Sort*} [FinEncodable ι] [∀i, FinEncodable (α i)] (
  f: ∀i, (Fin (card (α i)) ↭ α i) ⊕' Fin (card (α i)) ≃ α i
) : (∀i, Fin (card (α i)) ↭ α i) ⊕' (∀i, Fin (card (α i)) ≃ α i) :=
  if hf:∀i, is_inr (f i) then
    .inr (fun i => match h:(f i) with
      | .inr x => x
      | .inl _ => nomatch h ▸ (hf i))
  else
    .inl (fun i => match f i with
      | .inl x => x
      | .inr x => x.toBij)

end FinEncodable
