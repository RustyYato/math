import LeanMath.Data.Ordinal.Defs
import LeanMath.Data.Cardinal.Order
import LeanMath.Order.Set
import LeanMath.Order.Monotone

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

def enumOrd_nonempty.{u} {U: Set Ordinal.{u}} (hU: ¬U.BoundedAbove) (x: Ordinal.{u}) :
  (U ∩ Set.ofMem fun y => ∀(o': Ordinal), o' < x -> enumOrd U o' < y).Nonempty := by
  rw [Set.not_bddAbove_iff] at hU
  have ⟨a, ha⟩ := boundedAbove_of_small <| (Set.Iio x).image (enumOrd U)
  obtain ⟨b, hb, hba⟩ := hU a
  refine ⟨b, hb, fun c hc ↦ lt_of_le_of_lt ?_ hba⟩
  apply ha
  apply Set.mem_image'
  assumption

private theorem enumOrd_mem_aux (hs : ¬s.BoundedAbove) (o : Ordinal) :
    enumOrd s o ∈ s ∩ Set.ofMem fun b => ∀ c, c < o → enumOrd s c < b := by
  rw [enumOrd]
  exact csInf_mem (enumOrd_nonempty hs o)

variable {s: Set Ordinal}

def enumOrd_mem (hs : ¬s.BoundedAbove) (o : Ordinal) : enumOrd s o ∈ s :=
  (enumOrd_mem_aux hs o).1

def enumOrd_strictMono (hs : ¬s.BoundedAbove) : StrictMonotone (enumOrd s) :=
  fun a b ↦ (enumOrd_mem_aux hs b).2 a

def enumOrd_injective (hs : ¬s.BoundedAbove) : Function.Injective (enumOrd s) :=
  (enumOrd_strictMono hs).inj

def enumOrd_inj (hs : ¬s.BoundedAbove) {a b : Ordinal} : enumOrd s a = enumOrd s b ↔ a = b :=
  (enumOrd_injective hs).eq_iff

def enumOrd_le_enumOrd (hs : ¬s.BoundedAbove) {a b : Ordinal} :
    enumOrd s a ≤ enumOrd s b ↔ a ≤ b :=
  (enumOrd_strictMono hs).le_iff_le

def enumOrd_lt_enumOrd (hs : ¬s.BoundedAbove) {a b : Ordinal} :
    enumOrd s a < enumOrd s b ↔ a < b :=
  (enumOrd_strictMono hs).lt_iff_lt

def le_enumOrd_self (hs : ¬s.BoundedAbove) (o: Ordinal) : o ≤ enumOrd s o := by
  induction o with
  | ind o ih =>
  apply not_lt.mp
  intro h
  have := not_lt.mpr ((enumOrd_strictMono hs).le_iff_le.mp (ih _ h))
  contradiction

def range_enumOrd (hs : ¬s.BoundedAbove) : Set.range (enumOrd s) = s := by
  ext o
  let t := Set.ofMem fun x => o ≤ enumOrd s x
  apply Iff.intro
  · rintro ⟨b, rfl⟩
    exact enumOrd_mem hs b
  · intro ha
    refine ⟨sInf t, ?_⟩
    apply le_antisymm (enumOrd_le_of_forall_lt ha ?_) ?_
    · intro b hb
      apply not_le.mp
      intro hb'
      exact not_le.mpr hb (sInf_le _ _ hb')
    · apply csInf_mem (U := t)
      exists o
      apply le_enumOrd_self
      assumption

def enumOrd_surj (hs : ¬s.BoundedAbove) (hx: x ∈ s) : x ∈ Set.range (enumOrd s) := by
  rwa [range_enumOrd hs]

-- def IsInitial

def initialOrd : Ordinal.{u} ≃o { o: Ordinal.{u} // IsInitial o } where
  toFun := {
    val := enumOrd (Set.ofMem IsInitial)
  }
  invFun := sorry

end Ordinal
