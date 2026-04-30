import LeanMath.Data.Fintype.Defs
import LeanMath.Data.FinEncodable.Pairing

namespace Fintype

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α ⊕' β) where
  card := card α + card β
  repr :=
    fa.repr.bind fun fa =>
    fb.repr.map fun fb =>
    let ra := fa.toFinEncodable
    let rb := fb.toFinEncodable
    let : FinEncodable (α ⊕' β) :=
      @FinEncodable.instPSum _ _ ra rb
    Repr.ofFinEncodable _

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α ×' β) where
  card := card α * card β
  repr :=
    fa.repr.bind fun fa =>
    fb.repr.map fun fb =>
    let ra := fa.toFinEncodable
    let rb := fb.toFinEncodable
    let : FinEncodable (α ×' β) :=
      @FinEncodable.instPProd _ _ ra rb
    Repr.ofFinEncodable _

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α ⊕ β) :=
  ofEquiv Equiv.sum_equiv_psum.symm

instance [fa: Fintype α] [fb: Fintype β] : Fintype (α × β) :=
  ofEquiv Equiv.prod_equiv_pprod.symm

end Fintype

namespace Finite

instance [fa: Finite α] [fb: Finite β] : Finite (α ⊕' β) := by
  obtain ⟨fa⟩ := fa
  obtain ⟨fb⟩ := fb
  infer_instance

instance [fa: Finite α] [fb: Finite β] : Finite (α ×' β) := by
  obtain ⟨fa⟩ := fa
  obtain ⟨fb⟩ := fb
  infer_instance

instance [fa: Finite α] [fb: Finite β] : Finite (α ⊕ β) := by
  obtain ⟨fa⟩ := fa
  obtain ⟨fb⟩ := fb
  infer_instance

instance [fa: Finite α] [fb: Finite β] : Finite (α × β) := by
  obtain ⟨fa⟩ := fa
  obtain ⟨fb⟩ := fb
  infer_instance

end Finite
