import LeanMath.Data.Ordinal.Defs
import LeanMath.Data.Cardinal.Order
import LeanMath.Order.Set

namespace Cardinal

open Classical

instance (a: Cardinal.{u}) : Small.{u} (Set.Iic a) := by
  rw [←Cardinal.out_spec a]
  refine Small.of_surj (β := Set a.out) (fun x => ?_) ?_
  exact {
    val := type x
    property := by
      refine ⟨?_⟩
      apply Embedding.subtype_val
  }
  intro ⟨x, hx⟩
  induction x using ind with | type α =>
  obtain ⟨hx⟩ := hx
  exists Set.range hx
  ext; simp
  apply sound
  exact (Equiv.ofBij (Bijection.embed_eqv_range hx)).symm

def boundedAbove_iff_small (U: Set Cardinal.{u}) : Set.BoundedAbove U ↔ Small.{u} U := by
  apply Iff.intro
  · intro ⟨u, hu⟩
    apply Small.subset (b := Set.Iic u)
    intro x hx
    apply hu
    assumption
  · intro ⟨ι, h⟩
    exists sum (fun i: ι => (h.symm i).val)
    intro c hc
    induction c using ind with | type α =>
    let i := h ⟨_, hc⟩
    have ⟨eqv⟩ := exact (Cardinal.out_spec (type α))
    refine ⟨?_⟩
    dsimp
    apply Embedding.comp
    show (h.symm i).val.out ↪ Σi, (h.symm i).val.out
    exact {
      toFun x := ⟨i, x⟩
      inj := by
        intro a b h
        exact eq_of_heq (Sigma.mk.inj h).right
    }
    unfold i
    rw [Equiv.coe_symm]
    exact eqv.symm.toEmbedding

def boundedAbove_small (U: Set Cardinal.{u}) [Small.{u} U] : Set.BoundedAbove U := by
  rwa [boundedAbove_iff_small]

def boundedAbove_range {ι: Type u} (f: ι -> Cardinal.{u}) : Set.BoundedAbove (Set.range f) := by
  apply boundedAbove_small

end Cardinal

namespace Ordinal

open Classical

def boundedAbove_range {ι: Type u} (f: ι -> Ordinal.{u}) : Set.BoundedAbove (Set.range f) := by
    exists (⨆i, (f i).card.succ).ord
    rintro a ⟨i, rfl⟩
    apply le_of_lt
    apply Cardinal.lt_ord_of_card_lt
    apply lt_of_lt_of_le
    apply Cardinal.lt_succ
    apply  le_csSup _
    apply Set.mem_range'
    apply Cardinal.boundedAbove_range

def boundedAbove_of_small (U: Set Ordinal.{u}) [hs: Small.{u} U] : U.BoundedAbove := by
  obtain ⟨β, eqv⟩ := hs
  have ⟨bound, hbound⟩ := boundedAbove_range fun x => (eqv.symm x).val
  exists bound; intro u hu
  apply hbound
  simp; exists eqv ⟨u, hu⟩
  simp

noncomputable def enumOrd (U: Set Ordinal.{u}) (o: Ordinal.{u}) : Ordinal.{u} :=
  sInf (U ∩ Set.ofMem fun x => ∀(o': Ordinal), o' < o -> enumOrd U o' < x)
termination_by o

def enumOrd_le_of_forall_lt (ha : a ∈ s) (H : ∀ b < o, enumOrd s b < a) : enumOrd s o ≤ a := by
  rw [enumOrd]
  apply sInf_le
  exact ⟨ha, H⟩

def enumOrd_nonempty.{u} (U: Set Ordinal.{u}) (hU: ¬U.BoundedAbove) (x: Ordinal.{u}) :
  (U ∩ Set.ofMem fun y => ∀(o': Ordinal), o' < x -> enumOrd U o' < y).Nonempty := by
  rw [Set.not_bddAbove_iff] at hU
  have ⟨a, ha⟩ := boundedAbove_of_small <| (Set.Iio x).image (enumOrd U)
  obtain ⟨b, hb, hba⟩ := hU a
  refine ⟨b, hb, fun c hc ↦ lt_of_le_of_lt ?_ hba⟩
  apply ha
  apply Set.mem_image'
  assumption

#print axioms enumOrd_nonempty

end Ordinal
