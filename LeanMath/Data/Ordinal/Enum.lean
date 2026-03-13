import LeanMath.Data.Ordinal.Defs
import LeanMath.Order.Set

namespace Ordinal

noncomputable def enumOrd (U: Set Ordinal.{u}) (o: Ordinal.{u}) : Ordinal.{u} :=
  sInf (U ∩ Set.ofMem fun x => ∀(o': Ordinal), o' < o -> enumOrd U o' < x)
termination_by o

def enumOrd_le_of_forall_lt (ha : a ∈ s) (H : ∀ b < o, enumOrd s b < a) : enumOrd s o ≤ a := by
  rw [enumOrd]
  apply sInf_le
  exact ⟨ha, H⟩

-- def enumOrd_nonempty (U: Set Ordinal) (hU: ¬U.BoundedAbove) (x: Ordinal) :
--   (U ∩ Set.ofMem fun y => ∀(o': Ordinal), o' < x -> enumOrd U o' < y).Nonempty := by
--   sorry

end Ordinal
