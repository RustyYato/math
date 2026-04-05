import LeanMath.Data.Set.Defs
import LeanMath.Data.Equiv.Basic
import LeanMath.Order.CompleteLattice

structure Topology (α: Type*) where
  -- the set of open sets
  protected IsOpen : Set α -> Prop
  protected open_univ: IsOpen ⊤
  protected open_sUnion (U: Set (Set α)) (hU: ∀u ∈ U, IsOpen u) : IsOpen (⋃ U)
  protected open_inter (a b: Set α) (ha: IsOpen a) (hb: IsOpen b) : IsOpen (a ∩ b)

class TopologicalSpace (α: Type*) extends Topology α where

export TopologicalSpace (toTopology)

namespace Topology

variable {α β γ: Type*} (t: Topology α) (u: Topology β) (v: Topology γ)

def OpenSets : Set (Set α) where
  Mem := t.IsOpen
def OpenSets_inj: Function.Injective (α := Topology α) (fun a => a.OpenSets) := by
  intro a b h
  cases a; cases b; congr
  cases h; rfl
def OpenSets.univ : ⊤ ∈ t.OpenSets := t.open_univ
def OpenSets.inter {a b: Set α} : a ∈ t.OpenSets -> b ∈ t.OpenSets -> a ∩ b ∈ t.OpenSets := t.open_inter _ _
def OpenSets.sUnion {U: Set (Set α)} : (∀u ∈ U, u ∈ t.OpenSets) -> ⋃ U ∈ t.OpenSets := t.open_sUnion _
def OpenSets.empty : ⊥ ∈ t.OpenSets := by
  rw [←Set.sUnion_empty]
  apply sUnion
  nofun

def ClosedSets : Set (Set α) where
  Mem s := sᶜ ∈ t.OpenSets
def ClosedSets.univ : ⊤ ∈ t.ClosedSets := by
  show ⊤ᶜ ∈ t.OpenSets
  simp; apply OpenSets.empty
def ClosedSets.empty : ⊥ ∈ t.ClosedSets := by
  show ⊥ᶜ ∈ t.OpenSets
  simp; apply OpenSets.univ
def ClosedSets.sInter (U: Set (Set α)) (hU: ∀u ∈ U, u ∈ t.ClosedSets) : ⋂ U ∈ t.ClosedSets := by
  show _ᶜ ∈ t.OpenSets
  simp; apply OpenSets.sUnion
  intro u hu
  simp at hu
  have : _ ∈ t.OpenSets := hU _ hu
  simpa using this
def ClosedSets.union {a b: Set α} : a ∈ t.ClosedSets -> b ∈ t.ClosedSets -> a ∪ b ∈ t.ClosedSets := by
  intro ha hb
  show _ᶜ ∈ t.OpenSets
  simp; apply OpenSets.inter
  assumption
  assumption

-- the interior of a set is the union of all open subsets
def Interior (U: Set α) : Set α := ⋃ (t.OpenSets ∩ U.powerset)
-- the closure of a set is the intersection fo all closed supersets
def Closure (U: Set α) : Set α := ⋂ (t.ClosedSets ∩ Set.ofMem (U ⊆ ·))

class IsContinuous (f : α → β) (t: Topology α) (u: Topology β) : Prop where
  isOpen_preimage : ∀s ∈ u.OpenSets, s.preimage f ∈ t.OpenSets

def OpenSets.preimage (f: α -> β) [IsContinuous f t u] : ∀s ∈ u.OpenSets, s.preimage f ∈ t.OpenSets :=
  IsContinuous.isOpen_preimage

def OpenSets.preimage_at (f: α -> β) [IsContinuous f t u] : ∀s ∈ u.OpenSets, s.preimage f ∈ t.OpenSets :=
  IsContinuous.isOpen_preimage

def IsOpen.Interior (s: Set α) : t.Interior s ∈ t.OpenSets := by
  apply OpenSets.sUnion
  intro x hx
  exact hx.left

protected instance IsContinuous.id : IsContinuous (fun x: α => x) t t where
  isOpen_preimage _ := id

instance IsContinuous.const [LEM] (x: β) : IsContinuous (fun _: α => x) t u where
  isOpen_preimage s sopen := by
    rcases em (x ∈ s) with h | h
    suffices s.preimage (fun _: α => x) = (⊤: Set α) by
      rw [this]
      apply OpenSets.univ
    apply Set.ext_univ
    intro
    assumption
    suffices s.preimage (fun _: α => x) = ∅ by
      rw [this]
      apply OpenSets.empty
    apply Set.ext_empty
    intro
    assumption

@[implicit_reducible]
def IsContinuous.comp (f: β -> γ) (g: α -> β) [IsContinuous f u v] [IsContinuous g t u] : IsContinuous (f ∘ g) t v where
  isOpen_preimage s hs := by
    show Set.preimage g (Set.preimage f s) ∈ _
    apply OpenSets.preimage t u g
    apply OpenSets.preimage u v f
    assumption

-- the discrete topology
instance : Bot (Topology α) where
  bot := {
    IsOpen _ := True
    open_univ := True.intro
    open_sUnion _ _ := True.intro
    open_inter _ _ _ _ := True.intro
  }

inductive IsTrivial : Set α -> Prop where
| empty : IsTrivial ⊥
| univ : IsTrivial ⊤

-- the trivial topology
instance [LEM] : Top (Topology α) where
  top := {
    IsOpen := IsTrivial
    open_univ := IsTrivial.univ
    open_sUnion := by
      intro U hU
      rcases em (⊤ ∈ U) with htop | htop
      rw [show ⋃ U = ⊤ from ?_]; apply IsTrivial.univ
      ext; simp; exists ⊤
      rw [show ⋃ U = ⊥ from ?_]; apply IsTrivial.empty
      ext; simp
      intro x hx g
      cases hU x hx
      contradiction
      contradiction
    open_inter := by
      intro a b ha hb
      cases ha <;> cases hb
      all_goals simp
      iterate 3 apply IsTrivial.empty
      apply IsTrivial.univ
  }

inductive Generate (U: Set (Set α)) : Set α -> Prop where
| of (u: Set α) : u ∈ U -> Generate U u
| univ : Generate U ⊤
| inter {a b: Set α} : Generate U a -> Generate U b -> Generate U (a ∩ b)
| sUnion {V: Set (Set α)} : (∀v ∈ V, Generate U v) -> Generate U (⋃ V)

@[implicit_reducible]
def generate (U: Set (Set α)) : Topology α where
  IsOpen := Generate U
  open_univ := Generate.univ
  open_sUnion _ := Generate.sUnion
  open_inter _ _ := Generate.inter

def of_mem_generate
  {γ: Type u}
  {a: Set γ} {U: Set (Set γ)}
  (h: a ∈ (generate U).OpenSets)
  (t: Topology γ)
  (ht: ∀x ∈ U, x ∈ t.OpenSets) : a ∈ t.OpenSets := by
  replace h : Generate U a := h
  induction h with
  | of => apply ht; assumption
  | univ => apply OpenSets.univ
  | inter => apply OpenSets.inter <;> assumption
  | sUnion => apply OpenSets.sUnion <;> assumption

def mem_generate_of
  {γ: Type u}
  {a: Set γ} {U: Set (Set γ)}
  (h: a ∈ U) : a ∈ (generate U).OpenSets := by
  apply Generate.of
  assumption

instance : InfSet (Topology α) where
  sInf U := generate (⋃ (U.image (fun t => t.OpenSets)))

instance : Min (Topology α) where
  min a b := generate (a.OpenSets ∪ b.OpenSets)

instance : SupSet (Topology α) where
  sSup U := {
    IsOpen a := a ∈ sInf (U.image (fun t => t.OpenSets))
    open_univ := by
      rintro _ ⟨t, ht, rfl⟩
      apply OpenSets.univ
    open_sUnion := by
      rintro V hV _ ⟨t, ht, rfl⟩
      apply OpenSets.sUnion
      intro u hu
      apply hV u hu
      apply Set.mem_image'
      assumption
    open_inter := by
      rintro a b ha hb _ ⟨t, ht, rfl⟩
      apply OpenSets.inter
      apply ha
      apply Set.mem_image'
      assumption
      apply hb
      apply Set.mem_image'
      assumption
  }

instance : Max (Topology α) where
  max a b := {
    IsOpen x := x ∈ a.OpenSets ∩ b.OpenSets
    open_univ := by
      apply And.intro
      apply OpenSets.univ
      apply OpenSets.univ
    open_sUnion := by
      intro U hU
      apply And.intro
      apply OpenSets.sUnion
      intro u hu
      exact (hU u hu).left
      apply OpenSets.sUnion
      intro u hu
      exact (hU u hu).right
    open_inter := by
      intro x y hx hy
      apply And.intro
      apply OpenSets.inter
      exact hx.left
      exact hy.left
      apply OpenSets.inter
      exact hx.right
      exact hy.right
  }

def max_eq_sSup (a b: Topology α) : a ⊔ b = sSup {a, b} := by
  apply OpenSets_inj
  show _ ∩ _ = sInf _
  simp

def min_eq_sInf (a b: Topology α) : a ⊓ b = sInf {a, b} := by
  show generate _ = generate _
  congr
  simp

instance : LE (Topology α) where
  le a b := b.OpenSets ⊆ a.OpenSets
instance : LT (Topology α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

variable [LEM]

def mem_sSup (a: Set α) (U: Set (Topology α)) :
  a ∈ (sSup U).OpenSets ↔ ∀t ∈ U, a ∈ t.OpenSets := by
  apply Iff.intro
  rintro ha t ht
  exact ha t.OpenSets (Set.mem_image' ht)
  rintro ht _ ⟨_, _, rfl⟩
  apply ht
  assumption

private protected def sInf_le (U: Set (Topology α)) (u: (Topology α)) (hu: u ∈ U) : ⨅ U ≤ u := by
  intro x hx
  apply mem_generate_of
  refine ⟨u.OpenSets, ?_, ?_⟩
  apply Set.mem_image'
  assumption
  assumption
private protected def le_sInf (U: Set (Topology α)) (x: (Topology α)) : (∀u ∈ U, x ≤ u) -> x ≤ ⨅ U := by
  intro hx a ha
  apply of_mem_generate ha
  intro _ ⟨_, ⟨t, ht, rfl⟩, hx'⟩
  apply hx
  assumption
  assumption
private protected def le_sSup (U: Set (Topology α)) (u: (Topology α)) (hu: u ∈ U) : u ≤ ⨆ U := by
  intro a b
  rw [mem_sSup] at b
  apply b
  assumption
private protected def sSup_le (U: Set (Topology α)) (x: (Topology α)) : (∀u ∈ U, u ≤ x) -> ⨆ U ≤ x := by
  intro h b
  rw [mem_sSup]
  intro _ _ _
  apply h
  assumption
  assumption

instance : IsCompleteLattice (Topology α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl _ := Set.sub_refl _
  trans := flip Set.sub_trans
  antisymm {a b} ha hb := by
    apply OpenSets_inj
    apply Set.sub_antisymm <;> assumption
  max_le := by
    intro x a b ha hb
    rw [max_eq_sSup]
    apply sSup_le
    intro u hu
    simp at hu
    rcases hu with rfl | rfl <;> assumption
  left_le_max := by
    intro a b
    rw [max_eq_sSup]
    apply le_sSup
    simp
  right_le_max := by
    intro a b
    rw [max_eq_sSup]
    apply le_sSup
    simp
  min_le_left := by
    intro a b
    rw [min_eq_sInf]
    apply sInf_le
    simp
  min_le_right := by
    intro a b
    rw [min_eq_sInf]
    apply sInf_le
    simp
  le_min := by
    intro x a b ha hb
    rw [min_eq_sInf]
    apply le_sInf
    simp [ha, hb]
  sInf_le := sInf_le
  le_sInf := le_sInf
  le_sSup := le_sSup
  sSup_le := sSup_le
  le_top := by
    intro a _ h
    cases h
    apply OpenSets.empty
    apply OpenSets.univ
  bot_le := by
    intro _ _ _
    trivial

@[implicit_reducible]
def induced (f: α -> β) (tβ: Topology β) : Topology α where
  IsOpen s := ∃t ∈ tβ.OpenSets, t.preimage f = s
  open_univ := by
    exists ⊤
    apply And.intro
    apply OpenSets.univ
    rfl
  open_inter := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a ∩ b, ?_, ?_⟩
    apply OpenSets.inter <;> assumption
    ext; apply Iff.rfl
  open_sUnion := by
    intro U hU
    let V : Set (Set β) := {
      Mem v := ∃x ∈ U, v ∈ tβ.OpenSets ∧ v.preimage f = x
    }
    -- have ⟨sel, hsel⟩ := Classical.axiomOfChoice (fun a: U => hU a.val a.property)
    refine ⟨⋃ V, ?_, ?_⟩
    apply OpenSets.sUnion
    intro u ⟨_, _, _, rfl⟩
    assumption
    ext a
    apply Iff.intro
    · rintro ⟨u, ⟨_, hu, u_in_U, rfl⟩, heq_⟩
      exists u.preimage f
    · rintro ⟨u, u_in_u, hu⟩
      simp
      obtain ⟨t, ht, rfl⟩ := hU u u_in_u
      refine ⟨t.preimage f, ?_, ?_⟩
      refine ⟨t, ?_, rfl⟩
      exists t.preimage f
      assumption

@[implicit_reducible]
def coinduced (f: α -> β) (tα: Topology α) : Topology β where
  IsOpen s := s.preimage f ∈ tα.OpenSets
  open_univ := OpenSets.univ _
  open_inter := by
    intro a b ha hb
    show a.preimage f ∩ b.preimage f ∈ _
    apply OpenSets.inter
    assumption
    assumption
  open_sUnion := by
    intro U hU
    rw [show (⋃U).preimage f = ⋃(U.image fun x => x.preimage f) from ?_]
    apply OpenSets.sUnion
    rintro _ ⟨u, hu, rfl⟩
    apply hU
    assumption
    ext a
    apply Iff.intro
    · intro ⟨u, hu, hfa⟩
      refine ⟨u.preimage f, ?_, ?_⟩
      apply Set.mem_image'
      assumption
      assumption
    · intro ⟨_, ⟨u, hu, rfl⟩, ha⟩
      exists u

end Topology

structure TopologyEquiv {α β: Type*} (t: Topology α) (u: Topology β) extends α ≃ β where
  toFun_continuous : Topology.IsContinuous toFun t u
  invFun_continuous : Topology.IsContinuous invFun u t

infixr:50 " ≃ₜ " => fun α β [TopologicalSpace α] [TopologicalSpace β] => @TopologyEquiv α β toTopology toTopology
infixr:50 " ≃ᵗ " => TopologyEquiv

namespace TopologyEquiv

instance [tα: TopologicalSpace α] [tβ: TopologicalSpace β] : EquivLike (α ≃ₜ β) α β where

instance {t: Topology α} {u: Topology β} : EquivLike (TopologyEquiv t u) α β where

def id (t: Topology α) : t ≃ᵗ t where
  toEquiv := Equiv.id _
  toFun_continuous := Topology.IsContinuous.id _
  invFun_continuous := Topology.IsContinuous.id _

def symm {t: Topology α} {u: Topology β} (f: t ≃ᵗ u) : u ≃ᵗ t where
  toEquiv := f.toEquiv.symm
  toFun_continuous := f.invFun_continuous
  invFun_continuous := f.toFun_continuous

instance {t: Topology α} {u: Topology β} (f: t ≃ᵗ u) : Topology.IsContinuous f t u :=
  f.toFun_continuous
instance {t: Topology α} {u: Topology β} (f: t ≃ᵗ u) : Topology.IsContinuous f.symm u t :=
  f.invFun_continuous

def comp {t: Topology α} {u: Topology β} {v: Topology γ} (f: u ≃ᵗ v) (g: t ≃ᵗ u) : t ≃ᵗ v where
  toEquiv := f.toEquiv.comp g.toEquiv
  toFun_continuous := Topology.IsContinuous.comp _ u _ f g
  invFun_continuous := Topology.IsContinuous.comp _ u _ g.symm f.symm

def trans {t: Topology α} {u: Topology β} {v: Topology γ} (f: t ≃ᵗ u) (g: u ≃ᵗ v) : t ≃ᵗ v := g.comp f

@[simp] def apply_id (α: Sort*) (x: α) : Equiv.id α x = x := rfl
@[simp] def apply_comp (f: β ≃ γ) (g: α ≃ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_trans (f: β ≃ γ) (g: α ≃ β) (x: α) : (g.trans f) x = f (g x) := rfl

@[simp] def symm_coe (f: α ≃ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] def coe_symm (f: α ≃ β) (x: α) : f.symm (f x) = x := f.rightInv _

@[simp] def symm_symm (f: α ≃ β) : f.symm.symm = f := rfl

@[simp] def trans_assoc (f: α ≃ β) (g: β ≃ γ) (h: γ ≃ γ') :
  f.trans (g.trans h) = (f.trans g).trans h := rfl

@[simp] def symm_trans (f: α ≃ β) : f.symm.trans f = .id _ := by
  apply DFunLike.ext; intro x
  simp
@[simp] def trans_symm (f: α ≃ β) : f.trans f.symm = .id _ := by
  apply DFunLike.ext; intro x
  simp
@[simp] def id_symm : (Equiv.id _).symm = (Equiv.id α) := rfl
@[simp] def id_trans (f: α ≃ β) : (Equiv.id _).trans f = f := rfl
@[simp] def trans_id (f: α ≃ β) : f.trans (Equiv.id _) = f := rfl

def inj (f: α ≃ β) : Function.Injective f := f.rightInv.injective
def surj (f: α ≃ β) : Function.Surjective f := f.symm.rightInv.surjective

end TopologyEquiv

namespace Topology

variable [LEM]

def prod (t: Topology α) (u: Topology β) : Topology (α × β) :=
  induced Prod.fst t ⊓ induced Prod.snd u
def sum (t: Topology α) (u: Topology β) : Topology (α ⊕ β) :=
  coinduced Sum.inl t ⊔ coinduced Sum.inr u

@[implicit_reducible]
def IsContinuous.min_left (t₀ t₁: Topology α) (u: Topology β) (f: α -> β) (_: IsContinuous f t₀ u) : IsContinuous f (t₀ ⊓ t₁) u where
  isOpen_preimage s := by
    intro h
    apply mem_generate_of
    left
    apply OpenSets.preimage_at (u := u)
    assumption

@[implicit_reducible]
def IsContinuous.min_right (t₀ t₁: Topology α) (u: Topology β) (f: α -> β) (_: IsContinuous f t₁ u) : IsContinuous f (t₀ ⊓ t₁) u where
  isOpen_preimage s := by
    intro h
    apply mem_generate_of
    right
    apply OpenSets.preimage_at (u := u)
    assumption

@[implicit_reducible]
def IsContinuous.max_left (t: Topology α) (u₀ u₁: Topology β) (f: α -> β) (_: IsContinuous f t u₀) : IsContinuous f t (u₀ ⊔ u₁) where
  isOpen_preimage s := by
    intro h
    apply OpenSets.preimage_at _ _ f _ h.left

@[implicit_reducible]
def IsContinuous.max_right (t: Topology α) (u₀ u₁: Topology β) (f: α -> β) (_: IsContinuous f t u₁) : IsContinuous f t (u₀ ⊔ u₁) where
  isOpen_preimage s := by
    intro h
    apply OpenSets.preimage_at _ _ f _ h.right

protected instance IsContinuous.induced (u: Topology β) {f: α -> β} : IsContinuous f (induced f u) u where
  isOpen_preimage s hs := by exists s
protected instance IsContinuous.coinduced (t: Topology α) {f: α -> β} : IsContinuous f t (coinduced f t) where
  isOpen_preimage s hs := by assumption

@[implicit_reducible]
protected def IsContinuous.induced' (u: Topology β) {f: α -> β} : IsContinuous f (induced f u) u where
  isOpen_preimage s hs := by exists s
@[implicit_reducible]
protected def IsContinuous.coinduced' (t: Topology α) {f: α -> β} : IsContinuous f t (coinduced f t) where
  isOpen_preimage s hs := by assumption

instance (t: Topology α) (u: Topology β) : IsContinuous (Prod.fst: α × β -> α) (t.prod u) t := IsContinuous.min_left _ _ _ _ inferInstance
instance (t: Topology α) (u: Topology β) : IsContinuous (Prod.snd: α × β -> β) (t.prod u) u := IsContinuous.min_right _ _ _ _ inferInstance
instance (t: Topology α) (u: Topology β) : IsContinuous (Sum.inl: α -> α ⊕ β) t (t.sum u) := IsContinuous.max_left _ _ _ _ inferInstance
instance (t: Topology α) (u: Topology β) : IsContinuous (Sum.inr: β -> α ⊕ β) u (t.sum u) := IsContinuous.max_right _ _ _ _ inferInstance

def sigma {ι : Type*} {Y : ι → Type*} (t:  ∀i: ι, Topology (Y i)) : Topology (Σi: ι, Y i) :=
  ⨆i, coinduced (Sigma.mk i) (t i)

instance IsContinuous.sigma_mk {ι : Type*} {Y : ι → Type*} (t:  ∀i: ι, Topology (Y i)) (i: ι) : IsContinuous (Sigma.mk i) (t i) (sigma t) where
  isOpen_preimage := by
    intro U hU
    have := hU (coinduced (Sigma.mk i) (t i)).OpenSets (by
      apply Set.mem_image'
      apply Set.mem_range')
    apply this

def pi {ι : Type*} {Y : ι → Type*} (t:  ∀i: ι, Topology (Y i)) : Topology (∀i: ι, Y i) :=
  ⨅i, induced (fun f => f i) (t i)

abbrev func (α: Type*) {β: Type*} (u: Topology β) : Topology (α -> β) := pi (fun _ => u)

instance IsContinuous.apply_at {ι: Type*} {Y: ι -> Type*} (t:  ∀i: ι, Topology (Y i)) (i: ι) : IsContinuous (fun (f: ∀i, Y i) => f i) (pi t) (t i) where
  isOpen_preimage s hs := by
    apply mem_generate_of
    simp
    refine ⟨_, ⟨_, ⟨_, rfl⟩, rfl⟩, _, hs, rfl⟩

instance IsContinuous.apply (u: Topology β) : IsContinuous (fun (f: α -> β) a => f a) (func α u) (func α u) where
  isOpen_preimage s hs := by
    apply of_mem_generate hs
    intro u hu
    simp at hu
    obtain ⟨_, ⟨_, ⟨a, _, rfl⟩, rfl⟩, ⟨u, hu, rfl⟩⟩ := hu
    apply mem_generate_of
    simp
    exact ⟨_, ⟨_, ⟨_, rfl⟩, rfl⟩, _, hu, rfl⟩

instance IsContinuous.prod_mk (t: Topology α) (u: Topology β) : IsContinuous (Prod.mk : α -> β -> α × β) t (pi fun _ => t.prod u) where
  isOpen_preimage s hs := by
    induction hs with
    | univ => apply OpenSets.univ
    | inter =>
      show Set.preimage _ _ ∩ Set.preimage _ _ ∈ _
      apply OpenSets.inter <;> assumption
    | @sUnion U hU ih =>
      rw [Set.preimage_sUnion]
      apply OpenSets.sUnion
      rintro _ ⟨u, hu, rfl⟩
      apply ih
      assumption
    | of u hu =>
      simp at hu
      obtain ⟨_, ⟨_, ⟨b, ⟨_, _, rfl⟩, rfl⟩, rfl⟩, p, hp, rfl⟩ := hu
      simp
      rw [Function.comp_def]
      induction hp with
      | univ => apply OpenSets.univ
      | inter =>
        show Set.preimage _ _ ∩ Set.preimage _ _ ∈ _
        apply OpenSets.inter <;> assumption
      | @sUnion U hU ih =>
        rw [Set.preimage_sUnion]
        apply OpenSets.sUnion
        rintro _ ⟨u, hu, rfl⟩
        apply ih
        assumption
      | of u hu =>
        rcases hu with hu | hu
        · obtain ⟨a, ha, rfl⟩ := hu
          rw [Set.preimage_preimage, Function.comp_def]
          dsimp
          assumption
        · obtain ⟨a, ha, rfl⟩ := hu
          rw [Set.preimage_preimage, Function.comp_def]
          dsimp
          apply OpenSets.preimage
          assumption

def prod_func_eq_func2 (t: Topology α) (u: Topology β) (v: Topology γ) :
  func α (func β v) ≃ᵗ func (α × β) v where
  toFun f a := f a.fst a.snd
  invFun f a b := f (a, b)
  leftInv _ := rfl
  rightInv _ := rfl
  toFun_continuous := {
    isOpen_preimage s hs := by
      induction hs with
      | univ => apply OpenSets.univ
      | inter => simp; apply OpenSets.inter <;> assumption
      | @sUnion U hU ih =>
        simp; apply OpenSets.sUnion
        rintro u ⟨u, hu, rfl⟩
        apply ih
        assumption
      | of u hu =>
        simp at hu; obtain ⟨_, ⟨_, ⟨a, b, rfl⟩, rfl⟩, u, hu, rfl⟩ := hu
        simp [Function.comp_def]
        apply mem_generate_of
        simp; refine ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ?_⟩
        refine ⟨?_, ?_, ?_⟩
        · exact u.preimage (fun f' => f' b)
        · apply mem_generate_of
          refine ⟨_, ⟨_, ⟨b, rfl⟩, rfl⟩, ?_⟩
          dsimp
          apply (IsContinuous.induced _).isOpen_preimage
          assumption
        · rfl
  }
  invFun_continuous := {
    isOpen_preimage s hs := by
      induction hs with
      | univ => apply OpenSets.univ
      | inter => simp; apply OpenSets.inter <;> assumption
      | @sUnion U hU ih =>
        simp; apply OpenSets.sUnion
        rintro u ⟨u, hu, rfl⟩
        apply ih
        assumption
      | of u hu =>
        simp at hu; obtain ⟨_, ⟨_, ⟨a, _, rfl⟩, rfl⟩, u, hu, rfl⟩ := hu
        simp; induction hu with
        | univ => apply OpenSets.univ
        | inter => simp; apply OpenSets.inter <;> assumption
        | @sUnion U hU ih =>
          simp; apply OpenSets.sUnion
          rintro u ⟨u, hu, rfl⟩
          apply ih
          assumption
        | of u hu =>
          simp at hu; obtain ⟨_, ⟨_, ⟨b, _, rfl⟩, rfl⟩, u, hu, rfl⟩ := hu
          -- obtain ⟨_, ⟨_, ⟨a, b, rfl⟩, rfl⟩, u, hu, rfl⟩ := hu
          simp [Function.comp_def]
          apply mem_generate_of
          simp; refine ⟨_, ⟨_, ⟨a, b, rfl⟩, rfl⟩, ?_⟩
          refine ⟨u, ?_, ?_⟩
          · assumption
          · rfl
  }

-- private instance IsContinuous.pi_comp'
--   [Topology γ'] (t: Topology α) (u: Topology β) [Topology γ]
--   (f: α × β -> γ) (ga: γ' -> α) (gb: γ' -> β) {hf: IsContinuous f} [hga: IsContinuous ga] [hgb: IsContinuous gb] : IsContinuous (fun x => f (ga x, gb x)) := by
--   sorry

-- instance IsContinuous.apply₂
--   (t: Topology α) (u: Topology β) [Topology γ]
--   (f: α -> β -> γ) [hf: IsContinuous f] (a: α) : IsContinuous (f a) := by
--   -- We want to show: the map b ↦ f a b is continuous
--   -- Observe that f a b = f (a, b)

--   -- Define the map that fixes the first argument
--   let g : β → α × β := fun b ↦ (a, b)

--   -- Show g is continuous
--   have hg : IsContinuous g := sorry
--     -- continuous_const.prod_mk continuous_id

--   -- Note that (f a) = (Function.uncurry f) ∘ g
--   -- Because: (Function.uncurry f) (g b) = (Function.uncurry f) (a, b) = f a b

--   -- Compose: continuous (Function.uncurry f) from hf, and continuous g from hg
--   exact IsContinuous.comp' _ _ hf hg

-- instance IsContinuous.pi_comp
--   [Topology γ'] (t: Topology α) (u: Topology β) [Topology γ]
--   (f: α -> β -> γ) (ga: γ' -> α) (gb: γ' -> β)
--   [hf: IsContinuous f] [hga: IsContinuous ga] [hgb: IsContinuous gb] : IsContinuous (fun x => f (ga x) (gb x)) := by
--   show IsContinuous (fun x => prod_func_eq_func2 f (ga x, gb x))
--   apply IsContinuous.pi_comp'
--   clear hga hgb ga gb
--   show IsContinuous fun a: α × β => f a.fst a.snd
--   refine { isOpen_preimage s hs := ?_ }
--   have := hf.isOpen_preimage {
--     Mem f' := ∃a b, f a = f' ∧ f a b ∈ s
--   } ?_

--   have := this

--   sorry

-- instance IsContinuous.comp₂
--   [Topology γ']  (t: Topology α) (u: Topology β) [Topology γ]
--   (f: α -> β -> γ) (ga: γ' -> α) (gb: γ' -> β) [hf: IsContinuous f] [hga: IsContinuous ga] [hgb: IsContinuous gb] : IsContinuous (fun x => f (ga x) (gb x)) where
--   isOpen_preimage s hs := by

--     sorry

-- def IsContinuous.comp₂'
--   [Topology γ'] (t: Topology α) (u: Topology β) [Topology γ]
--   (f: α -> β -> γ) (ga: γ' -> α) (gb: γ' -> β) (hf: IsContinuous f) (hga: IsContinuous ga) (hgb: IsContinuous gb) : IsContinuous (fun x => f (ga x) (gb x)) :=
--   IsContinuous.comp₂ _ _ _

-- def _root_.TopologyEquiv.prod_congr
--   {_: Topology α₀} {_: Topology α₁}
--   {_: Topology β₀} {_: Topology β₁}
--   (f: α₀ ≃ₜ α₁) (g: β₀ ≃ₜ β₁) : (α₀ × β₀) ≃ₜ (α₁ × β₁) where
--   toEquiv := Equiv.prod_congr f.toEquiv g.toEquiv
--   toFun_continuous := by
--     show IsContinuous (fun a: α₀ × β₀ => (f a.fst, g a.snd))
--     apply IsContinuous.comp₂'
--     infer_instance
--     apply IsContinuous.comp
--     apply IsContinuous.comp
--   invFun_continuous := by
--     show IsContinuous (fun a: α₁ × β₁ => (f.symm a.fst, g.symm a.snd))
--     apply IsContinuous.comp₂'
--     infer_instance
--     apply IsContinuous.comp
--     apply IsContinuous.comp

-- instance
--   (t: Topology α) (u: Topology β) [Topology γ]
--   (f: γ -> α)
--   (g: γ -> β)
--   [IsContinuous f]
--   [IsContinuous g]
--   : IsContinuous (fun x => (f x, g x)) := by
--     apply IsContinuous.comp₂' Prod.mk <;> infer_instance

end Topology

namespace TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

def OpenSets (α: Type*) [TopologicalSpace α] : Set (Set α) := toTopology.OpenSets
def OpenSets.univ : ⊤ ∈ OpenSets α := toTopology.open_univ
def OpenSets.inter {a b: Set α} : a ∈ OpenSets α -> b ∈ OpenSets α -> a ∩ b ∈ OpenSets α := toTopology.open_inter _ _
def OpenSets.sUnion {U: Set (Set α)} : (∀u ∈ U, u ∈ OpenSets α) -> ⋃ U ∈ OpenSets α := toTopology.open_sUnion _
def OpenSets.empty : ⊥ ∈ OpenSets α := Topology.OpenSets.empty _
def ClosedSets (α: Type*) [TopologicalSpace α] : Set (Set α) where
  Mem s := sᶜ ∈ OpenSets α
def ClosedSets.univ : ⊤ ∈ ClosedSets α := by
  show ⊤ᶜ ∈ OpenSets α
  simp; apply OpenSets.empty
def ClosedSets.empty : ⊥ ∈ ClosedSets α := by
  show ⊥ᶜ ∈ OpenSets α
  simp; apply OpenSets.univ
def ClosedSets.sInter (U: Set (Set α)) (hU: ∀u ∈ U, u ∈ ClosedSets α) : ⋂ U ∈ ClosedSets α := by
  show _ᶜ ∈ OpenSets α
  simp; apply OpenSets.sUnion
  intro u hu
  simp at hu
  have : _ ∈ OpenSets α := hU _ hu
  simpa using this
def ClosedSets.union {a b: Set α} : a ∈ ClosedSets α -> b ∈ ClosedSets α -> a ∪ b ∈ ClosedSets α := by
  intro ha hb
  show _ᶜ ∈ OpenSets α
  simp; apply OpenSets.inter
  assumption
  assumption

-- the interior of a set is the union of all open subsets
def Interior (U: Set α) : Set α := ⋃ (OpenSets α ∩ U.powerset)
-- the closure of a set is the intersection fo all closed supersets
def Closure (U: Set α) : Set α := ⋂ (ClosedSets α ∩ Set.ofMem (U ⊆ ·))

abbrev IsContinuous (f : α → β) := Topology.IsContinuous f toTopology toTopology

def OpenSets.preimage (f: α -> β) [IsContinuous f] : ∀s ∈ OpenSets β, s.preimage f ∈ OpenSets α :=
  Topology.OpenSets.preimage _ _ f

def IsOpen.Interior (s: Set α) : Interior s ∈ OpenSets α := by
  apply OpenSets.sUnion
  intro x hx
  exact hx.left

instance : TopologicalSpace ℕ := ⟨⊥⟩
instance : TopologicalSpace ℤ := ⟨⊥⟩

instance : TopologicalSpace (α × β) := ⟨toTopology.prod toTopology⟩
instance : TopologicalSpace (α ⊕ β) := ⟨toTopology.sum toTopology⟩
instance {ι: Type*} {α: ι -> Type*} [∀i, TopologicalSpace (α i)] : TopologicalSpace (∀i, α i) := ⟨Topology.pi (fun _ => toTopology)⟩
instance {ι: Type*} {α: ι -> Type*} [∀i, TopologicalSpace (α i)] : TopologicalSpace (Σi, α i) := ⟨Topology.sigma (fun _ => toTopology)⟩

instance {ι : Type*} {Y : ι → Type*} [∀i: ι, TopologicalSpace (Y i)] (i: ι) : IsContinuous (Sigma.mk (β := Y) i) :=
  Topology.IsContinuous.sigma_mk (fun _ => toTopology) _

instance {ι : Type*} {Y : ι → Type*} [∀i: ι, TopologicalSpace (Y i)] (i: ι) : IsContinuous (fun (f: ∀i, Y i) => f i) :=
  Topology.IsContinuous.apply_at (fun _ => toTopology) _

instance : IsContinuous (fun (f: α -> β) (a: α) => f a) := inferInstance

instance [LEM] : IsContinuous (Prod.mk : α -> β -> α × β) := Topology.IsContinuous.prod_mk toTopology toTopology

end TopologicalSpace
