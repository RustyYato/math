import LeanMath.Data.Cardinal.Defs
import LeanMath.Data.Ordinal.Defs
import LeanMath.Order.WellOrdering

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

def card : Ordinal -> Cardinal :=
  lift (fun {α} _ => Cardinal.type α) <| by
    intro _ _ _  _ _ _ h
    apply Cardinal.sound
    exact h.toEquiv

@[simp] def card_type (r: α -> α -> Prop) [Relation.IsWellOrder r] : card (type r) = Cardinal.type α := rfl

def card_surj : Function.Surjective card := by
  intro x
  cases x with | _ α =>
  exists (Ordinal.type (well_order α))

def IsInitial (o: Ordinal) : Prop := ∀x: Ordinal, o.card = x.card -> o ≤ x

def IsInitial.to_lt [LEM] (a b: Ordinal) (ha: a.IsInitial) (hb: b.IsInitial) : a < b -> a.card < b.card := by
  open Classical in
  intro h
  cases a with | @type α r =>
  cases b with | @type β s =>
  have ⟨f⟩ := h
  dsimp at f
  show Cardinal.type α < Cardinal.type β
  apply And.intro ⟨f.toEmbedding⟩
  intro ⟨g⟩
  replace g := Equiv.antisymm f.toEmbedding g
  have := hb (type r) ?_
  have := not_le_of_lt h
  contradiction
  apply Cardinal.sound
  dsimp; apply Equiv.symm
  assumption

def lt_of_card_lt [LEM] {a b: Ordinal} (h: a.card < b.card) : a < b := by
  apply not_le.mp
  induction a using Ordinal.ind with | @type α r =>
  induction b using Ordinal.ind with | @type β s =>
  replace h : Cardinal.type α < Cardinal.type β := h
  rw [lt_iff_le_and_not_ge] at h
  intro ⟨g⟩; dsimp at g
  obtain ⟨⟨h⟩, h'⟩ := h
  have := Equiv.antisymm h g.toEmbedding
  clear h
  apply h'
  refine ⟨?_⟩
  apply this.symm.toEmbedding

end Ordinal

namespace Cardinal

open Classical

private def exists_ord (c: Cardinal) : ∃o: Ordinal, o.card = c := by
  cases c with | type α =>
  exists Ordinal.type (well_order α)

-- the samllest ordinal which is has the cardinality of the input
noncomputable def ord : Cardinal ↪ Ordinal where
  toFun c := Relation.min (· < ·) c.exists_ord
  inj {a b} h := by
    dsimp at h
    have ha := Relation.min_spec (· < ·) a.exists_ord
    have hb := Relation.min_spec (· < ·) b.exists_ord
    rw [←ha, ←hb]
    congr
def ord_eq_sinf (c: Cardinal) : c.ord = sInf { Mem x := x.card = c } := by
  apply le_antisymm
  · apply le_csInf
    have ⟨o, ho⟩ := c.exists_ord
    exists o
    intro o ho
    apply not_lt.mp
    intro h; apply Relation.min_minimal (· < ·) (exists_ord c)
    assumption
    assumption
  · apply sInf_le
    apply Relation.min_spec _ c.exists_ord

def card_ord (c: Cardinal) : c.ord.card = c := Relation.min_spec (· < ·) (exists_ord c)
def ord_card (o: Ordinal) : o.card.ord ≤ o := by
  apply not_lt.mp
  intro h
  apply Relation.min_minimal (· < ·) (exists_ord o.card) _ _ rfl
  assumption
def to_ord_spec (c: Cardinal) : c.ord.IsInitial := by
  intro x hx
  rw [ord_eq_sinf]
  apply sInf_le
  show x.card = c
  rw [←hx, card_ord]

noncomputable def to_initial_ord : (· ≤ ·: Cardinal -> Cardinal -> Prop) ↪r (· ≤ ·: Ordinal -> Ordinal -> Prop) where
  toEmbedding := ord
  map_rel := by
    intro a b
    apply flip Iff.intro
    · intro h
      have ⟨α, r, hr, ha⟩ := a.ord.exists_eq_type
      have ⟨β, s, hs, hb⟩ := b.ord.exists_eq_type
      simp [ha, hb] at h
      obtain ⟨h⟩ := h; dsimp at h
      have ga := Relation.min_spec (· < ·) a.exists_ord
      have gb := Relation.min_spec (· < ·) b.exists_ord
      rw [←ga, ←gb]
      show a.ord.card ≤ b.ord.card
      rw [ha, hb]
      refine ⟨?_⟩
      exact h.toEmbedding
    · intro h
      classical
      apply le_of_not_lt
      intro g
      have := Ordinal.IsInitial.to_lt
        b.ord a.ord
        (to_ord_spec _)
        (to_ord_spec _)
        g
      have ga : a.ord.card = a := Relation.min_spec (· < ·) a.exists_ord
      have gb : b.ord.card = b := Relation.min_spec (· < ·) b.exists_ord
      rw [ga, gb] at this
      clear ga gb g
      have := not_le_of_lt this
      contradiction

noncomputable def to_initial_ord_lt : (· < ·: Cardinal -> Cardinal -> Prop) ↪r (· < ·: Ordinal -> Ordinal -> Prop) where
  toEmbedding := to_initial_ord.toEmbedding
  map_rel := by
    intro a b
    rw [lt_iff_le_and_not_ge, lt_iff_le_and_not_ge, map_rel to_initial_ord, map_rel to_initial_ord]
    rfl

instance : @Relation.IsTotal Cardinal (· ≤ ·) := to_initial_ord.liftTotal
instance : @Relation.IsTrichotomous Cardinal (· < ·) (· = ·) := inferInstance
instance : @Relation.IsWelFounded Cardinal (· < ·) := to_initial_ord_lt.liftWellfounded
instance : IsLinearOrder Cardinal where

instance : @Relation.IsWellOrder Cardinal (· < ·) where
  trichotomous := by
    intro a b; classical
    rcases Relation.total (α := Cardinal) (· ≤ ·) a b with h | h
    all_goals rcases lt_or_eq_of_le h with h | rfl
    left; assumption
    right; left; rfl
    right; right; assumption
    right; left; rfl

def card_lt_of_lt_ord {o: Ordinal} {c: Cardinal} : o < c.ord -> o.card < c := by
  intro h
  apply map_rel_rev to_initial_ord_lt
  show o.card.ord < c.ord
  apply lt_of_le_of_lt _ h
  apply ord_card

def lt_ord_of_card_lt {o: Ordinal} {c: Cardinal} : o.card < c -> o < c.ord := by
  intro h
  rw [ord_eq_sinf]
  have o_lt : ∀x: Ordinal, x.card = c -> o < x := by
    intro x rfl
    apply Ordinal.lt_of_card_lt
    assumption
  have := o_lt c.ord (card_ord _ ▸ rfl)
  apply lt_of_lt_of_le
  exact o_lt c.ord (card_ord _ ▸ rfl)
  apply le_csInf
  exists c.ord
  apply card_ord
  intro x hx
  rw [ord_eq_sinf]
  apply sInf_le
  assumption

def lt_ord {o: Ordinal} {c: Cardinal} : o < c.ord ↔ o.card < c := by
  apply Iff.intro
  apply card_lt_of_lt_ord
  apply lt_ord_of_card_lt

noncomputable instance : Min Cardinal := minOfLe
noncomputable instance : Max Cardinal := maxOfLe

noncomputable instance : InfSet Cardinal where
  sInf S :=
    open UniqueChoice in
    if h:S.Nonempty then
      Set.min (· < ·) h
    else
      0

def sInf_mem (U: Set Cardinal) (hU: U.Nonempty) : ⨅ U ∈ U := by
  simp [sInf]
  rw [dif_pos hU]
  apply Set.min_mem

private protected def sInf_le (U: Set Cardinal) : ∀u ∈ U, ⨅ U ≤ u := by
  intro u hu
  simp [sInf]
  rw [dif_pos ⟨_, hu⟩]
  apply le_of_not_lt
  intro h
  exact Set.min_minimal (· < ·) (U := U) ⟨_, hu⟩ u hu h

private protected def le_sInf (U: Set Cardinal) (hU: U.Nonempty) (x: Cardinal) (h: ∀u ∈ U, x ≤ u) : x ≤ ⨅ U := by
  classical
  apply le_of_not_lt
  intro g
  have (u: Cardinal) (hu: u ∈ U) : sInf U < u := by
    apply lt_of_lt_of_le g
    apply h
    assumption
  exact Relation.irrefl (this _ (sInf_mem  U hU))

noncomputable instance : SupSet Cardinal where
  sSup S := sInf S.upperBounds

protected def sSup_eq_sInf_upperBounds (U: Set Cardinal) : ⨆ U = ⨅ U.upperBounds := rfl

def min_eq (a b: Cardinal) : a ⊓ b = if a ≤ b then a else b := rfl
def max_eq (a b: Cardinal) : a ⊔ b = if a ≤ b then b else a := rfl

instance [LEM] : IsConditionallyCompleteLattice Cardinal where
  left_le_max {a b} := by
    rw [max_eq]; split
    assumption; rfl
  right_le_max {a b} := by
    rw [max_eq]; split
    rfl; apply le_of_lt
    apply not_le.mp; assumption
  max_le {x a b} ha hb := by
    rw [max_eq]; split <;> assumption
  min_le_left {a b} := by
    rw [min_eq]; split
    rfl; apply le_of_lt
    apply not_le.mp; assumption
  min_le_right {a b} := by
    rw [min_eq]; split
    assumption; rfl
  le_min {x a b} ha hb := by
    rw [min_eq]; split <;> assumption
  csInf_le _ := Cardinal.sInf_le _ _
  le_csInf h g := Cardinal.le_sInf _ h _ g
  le_csSup := by
    intro S a ha hs; rw [Cardinal.sSup_eq_sInf_upperBounds]
    apply le_sInf
    assumption
    intro u hu
    apply hu
    assumption
  csSup_le := by
    intro U a hU ha
    rw [Cardinal.sSup_eq_sInf_upperBounds]
    apply sInf_le
    assumption

instance [LEM] : IsLawfulInf Cardinal where
  sInf_le := Cardinal.sInf_le

noncomputable def succ (c: Cardinal.{u}) : Cardinal.{u} :=
  Set.min (· < ·) (U := Set.Ioi c) <| by
    exists 2 ^ c
    apply Cardinal.lt_two_pow

def lt_succ (c: Cardinal) : c < c.succ := by
  show c.succ ∈ Set.Ioi c
  apply Set.min_mem

def of_lt_succ (c: Cardinal) : ∀{x}, x < c.succ -> x ≤ c := by
  classical
  intro x hx; apply le_of_not_lt
  intro h
  exact Set.min_minimal (· < ·) (U := Set.Ioi c) ⟨_, h⟩ x h hx

def succ_le (c: Cardinal) : ∀{x}, c < x -> c.succ ≤ x := by
  classical
  intro x cx; apply le_of_not_lt
  intro h
  have := not_lt.mpr (of_lt_succ _ h)
  contradiction

def succ_finite (n: ℕ) : succ n = (n + 1: ℕ) := by
  open Classical in
  apply le_antisymm
  · apply succ_le
    rw [natCast_lt_natCast]
    apply Nat.lt_succ_self
  · classical
    apply le_of_not_lt
    intro h
    have ⟨m, hm⟩ := lt_omega_iff_natCast.mp (lt_trans h (natCast_lt_omega (n + 1)))
    rw [hm, natCast_lt_natCast, Nat.lt_succ_iff] at h
    rcases Or.symm (Nat.lt_or_eq_of_le h) with h | h
    subst m
    · have := lt_succ n
      rw [hm] at this
      exact Relation.irrefl this
    · rw [←natCast_lt_natCast, ←hm] at h
      apply not_le_of_lt h
      apply le_of_lt
      apply lt_succ

def omega_ne_succ : ∀{c: Cardinal}, c.succ ≠ ω := by
  intro c
  intro h
  have := lt_succ c
  rw [h] at this
  rw [lt_omega_iff_natCast] at this
  obtain ⟨n, rfl⟩ := this
  rw [succ_finite] at h
  have := natCast_lt_omega (n + 1)
  rw [h] at this
  exact Relation.irrefl this

def succ_lt_succ {a b: Cardinal} : a.succ < b.succ ↔ a < b := by
  classical
  apply Iff.intro
  · intro h
    apply lt_of_lt_of_le _ (of_lt_succ _ h)
    apply lt_succ
  · intro h
    have := succ_le _ h
    apply lt_of_le_of_lt
    exact succ_le _ h
    apply lt_succ

def succ_inj : Function.Injective succ := by
  intro a b eq
  rcases Relation.trichotomous (· < ·) a b with h | h | h
  rw [←succ_lt_succ, eq] at h
  nomatch Relation.irrefl h
  assumption
  rw [←succ_lt_succ, eq] at h
  nomatch Relation.irrefl h

end Cardinal

namespace Ordinal

open Classical in
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

open Classical in
def boundedAbove_of_small (U: Set Ordinal.{u}) [hs: Small.{u} U] : U.BoundedAbove := by
  obtain ⟨β, eqv⟩ := hs
  have ⟨bound, hbound⟩ := boundedAbove_range fun x => (eqv.symm x).val
  exists bound; intro u hu
  apply hbound
  simp; exists eqv ⟨u, hu⟩
  simp

def initialOrdinals : Set Ordinal := Set.ofMem Ordinal.IsInitial

def initialOrdinals_unbounded.{u} [LEM] : ¬initialOrdinals.{u}.BoundedAbove := by
  simp [Set.BoundedAbove]
  intro x hx
  suffices ∃o > x, o ∈ initialOrdinals by
    obtain ⟨o, x_lt_o, o_mem⟩ := this
    exact not_le_of_lt x_lt_o (hx o o_mem)
  clear hx
  let U : Set Ordinal.{u} := {
    Mem u := u.InjectsInto x
  }
  have Unonuniv : Uᶜ.Nonempty := by
    cases x with | @type α r =>
    let β : Type u := (S: Set α) × (R: S -> S -> Prop) ×' (Relation.IsWellOrder R)
    let ord : Set Ordinal.{u} := Set.range (fun (⟨S, R, _⟩: β) => type R)
    have : ord = U := by
      ext x
      cases x with | @type β s =>
      simp [ord, U, InjectsInto]
      apply Iff.intro
      · intro ⟨⟨S, R, _⟩, h⟩
        dsimp at h
        replace ⟨h⟩ := exact' h
        exact ⟨h.symm.toEmbedding.trans  Embedding.subtype_val⟩
      · intro ⟨f⟩
        let rel := pushfwd_rel s (Bijection.embed_eqv_range f) (Bijection.surj _)
        exists ⟨Set.range f, pushfwd_rel s (Bijection.embed_eqv_range f) (Bijection.surj _), inferInstance⟩
        have ⟨inv, hinv⟩ := Classical.axiomOfChoice (Bijection.embed_eqv_range f).surj
        replace hinv : ∀x: Set.range f, f (inv x) = x.val := by
          intro x
          exact congrArg Subtype.val (hinv x)
        dsimp; symm; apply sound
        exact {
          toFun x := {
            val := f x
            property := Set.mem_range'
          }
          invFun := inv
          leftInv x := by
            dsimp; congr
            rw [hinv]
          rightInv x := by
            apply inj f
            rw [hinv]
          map_rel {a b} := by
            apply Iff.intro
            intro h
            refine ⟨a, _, rfl, rfl, h⟩
            intro ⟨a, b, ha, hb, h⟩
            cases inj f (Subtype.mk.inj ha)
            cases inj f (Subtype.mk.inj hb)
            assumption
        }
    rw [←this]
    have ⟨ub, hub⟩ := boundedAbove_of_small ord
    exists ub.succ
    intro h
    exact not_le_of_lt (lt_succ_self _) (hub _ h)
  let ⟨u, ⟨umem,hu⟩, uniq⟩ := (Uᶜ).exists_unique_min (· < ·) Unonuniv
  clear uniq
  exists u
  apply And.intro
  · show _ < _
    apply not_le.mp
    intro h
    have : u ∈ U := injects_into_of_le h
    contradiction
  · intro o ho
    have : o ∈ Uᶜ := by
      cases u with | _ ru =>
      cases o with | _ ro =>
      cases x with | _ rx =>
      simp at ho
      obtain ⟨ho⟩ := Cardinal.exact ho
      intro ⟨hx⟩; dsimp at hx
      apply umem; exact ⟨ho.toEmbedding.trans hx⟩
    exact not_lt.mp (hu o this)

end Ordinal
