import LeanMath.Data.Ordinal.Basic
import LeanMath.Data.Cardinal.Order
import LeanMath.Order.Set
import LeanMath.Order.Monotone

namespace Ordinal

open Classical

noncomputable def enumOrd (U: Set Ordinal.{u}) (o: Ordinal.{u}) : Ordinal.{u} :=
  sInf (U ∩ Set.ofMem fun x => ∀(o': Ordinal), o' < o -> enumOrd U o' < x)
termination_by o

def enumOrd_le_of_forall_lt (ha : a ∈ s) (H : ∀ b < o, enumOrd s b < a) : enumOrd s o ≤ a := by
  rw [enumOrd]
  apply sInf_le
  exact ⟨ha, H⟩

@[implicit_reducible]
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

private def initialOrd_exists : type (α := Ordinal.{u}) (· < ·) = type (α := { o: Ordinal.{u} // IsInitial o }) (pullback_rel (· < ·) Embedding.subtype_val) := by
  symm; apply le_antisymm
  · refine ⟨?_⟩
    apply InitialSegment.collapse
    dsimp; exact {
      toEmbedding := Embedding.subtype_val
      map_rel := Iff.rfl
    }
  · refine ⟨?_⟩; dsimp
    apply InitialSegment.collapse
    exact {
      toFun x := {
        val := enumOrd initialOrdinals x
        property := enumOrd_mem initialOrdinals_unbounded _
      }
      inj := by
        intro a b h
        dsimp at h
        exact (enumOrd_inj initialOrdinals_unbounded).mp (Subtype.mk.inj h)
      map_rel {a b} := by
        apply (enumOrd_strictMono initialOrdinals_unbounded).lt_iff_lt.symm
    }

noncomputable def initialOrd : Ordinal.{u} ≃o { o: Ordinal.{u} // IsInitial o } where
  toEquiv := Equiv.ofBij {
    toFun x := {
      val := enumOrd initialOrdinals x
      property := enumOrd_mem initialOrdinals_unbounded _
    }
    inj' := by
      intro a b h
      dsimp at h
      exact (enumOrd_inj initialOrdinals_unbounded).mp (Subtype.mk.inj h)
    surj' := by
      intro o
      have ⟨i, hi⟩ := enumOrd_surj initialOrdinals_unbounded o.property
      exists i; ext; assumption
  }
  map_rel {a b} := (enumOrd_strictMono initialOrdinals_unbounded).le_iff_le.symm

def initialOrd_of_le_omega : ∀x ≤ ω, initialOrd.{u} x = x := by
  have : ∀x ≤ ω, IsInitial.{u} x := by
    intro x hx
    rcases lt_or_eq_of_le hx with hx | rfl
    · obtain ⟨n, rfl⟩ := lt_omega_iff.mp hx
      rename_i h; clear hx h
      intro o ho
      cases o with | @type α r =>
      replace ho : Nat.cast n = Cardinal.type α := ho
      apply le_of_eq
      have : Finite α := Finite.ofBij ((Equiv.ulift _).trans (Cardinal.exact' ho)).toBij
      have ⟨m, hm⟩ := Ordinal.finite r
      rw [hm]; congr
      have := Equiv.ulift_congr.symm ((Cardinal.exact' ho).trans (exact hm).toEquiv)
      exact Equiv.of_fin_eqv this
    · clear hx; intro o ho
      apply not_lt.mp; intro h
      cases o with | @type α r =>
      obtain ⟨f⟩ := h; dsimp at f
      replace f := f.trans_init (ulift_rel_eqv_rel _).toInitialSegment
      have ⟨n, htop⟩ := f.IsPrincipal
      have hf : ∀x, f x < n := by
        intro x
        apply (htop _).mpr
        apply Set.mem_range'
      have : Finite α := by
        apply Finite.ofEmbed (β := Fin n)
        exact {
          toFun a := ⟨f a, hf _⟩
          inj := by
            intro a b h
            dsimp at h
            exact f.inj (Fin.mk.inj h)
        }
      have ⟨m, h⟩ := finite r
      rw [h] at ho
      replace ho := Equiv.ulift_congr.symm (Cardinal.exact' ho)
      dsimp at ho
      let max := max_of_range ho.symm
      have : ∀x, x ≤ max := by
        intro x
        have := le_max_of_range (ho x) ho.symm
        simpa using this
      exact not_le_of_lt (Nat.lt_succ_self _) (this _)
  intro x hx
  have xinit := this x hx
  apply le_antisymm
  · sorry
  · sorry

noncomputable def omega : Ordinal.{u} ↪o { o: Ordinal.{u} // IsInitial o } :=
  order_emb_of_map_rel (initialOrd <| ω + ·) <| by
    intro x y
    dsimp
    apply Iff.trans _ (map_rel initialOrd)
    exact add_le_add_left_iff_le.symm

def omega_zero : omega 0 = ω := by
  show initialOrd (ω + 0) = ω
  rw [add_zero, initialOrd_of_le_omega]
  apply le_refl

noncomputable def cardInit : (· < ·: Ordinal -> Ordinal -> Prop) ≼r (· < ·: Cardinal -> Cardinal -> Prop) :=
  (toLtEquiv (Cardinal.equiv_initial_ord.symm.comp initialOrd)).toInitialSegment

end Ordinal

namespace Cardinal

open Classical

private noncomputable def aleph' : Ordinal.{u} ↪ Cardinal where
  toFun o := (Ordinal.omega o).val.card
  inj a b h := by
    dsimp at h
    apply inj Ordinal.omega
    apply le_antisymm
    exact (Ordinal.omega a).property _ h
    exact (Ordinal.omega b).property _ h.symm

noncomputable def aleph : Ordinal.{u} ↪o Cardinal where
  toEmbedding := aleph'
  map_rel {a b} := by
    apply Iff.intro
    intro h
    apply Ordinal.IsInitial.to_le
    apply Subtype.property
    apply Subtype.property
    show Ordinal.omega a ≤ Ordinal.omega b
    apply (map_le _ _ _).mp
    assumption
    intro h
    rcases lt_or_eq_of_le h with h | h
    · exact le_of_lt <| (map_lt Ordinal.omega _ _).mpr (Ordinal.lt_of_card_lt h)
    · rw [inj aleph' h]

end Cardinal

open Classical

noncomputable def RelEquiv.ordinal_eqv_cardinal : (· < ·: Ordinal -> Ordinal -> Prop) ≃r (· < ·: Cardinal -> Cardinal -> Prop) :=
  InitialSegment.antisymm Ordinal.cardInit (InitialSegment.collapse <| (toLtEmb (Cardinal.equiv_initial_ord)).trans RelEmbedding.subtype_val)

noncomputable def OrderEquiv.ordinal_eqv_cardinal : Ordinal ≃o Cardinal where
  toEquiv := RelEquiv.ordinal_eqv_cardinal.toEquiv
  map_rel {a b} := by
    rw [←not_lt, ←not_lt, map_rel RelEquiv.ordinal_eqv_cardinal]
    rfl

@[simp] def RelEquiv.apply_ordinal_eqv_cardinal (x: Ordinal) : RelEquiv.ordinal_eqv_cardinal x = (Ordinal.initialOrd x).val.card := rfl
@[simp] def OrderEquiv.apply_ordinal_eqv_cardinal (x: Ordinal) : OrderEquiv.ordinal_eqv_cardinal x = (Ordinal.initialOrd x).val.card := rfl
