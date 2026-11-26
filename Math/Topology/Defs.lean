module

public import Math.Order.CompleteLattice.Defs
public import Math.Order.GaloisConnection
public import Math.Tactic.Basic
import Math.Data.Set.Basic

namespace Math

@[ext]
public structure Topology (α: Type*) where
  OpenSets: Set (Set α)
  open_top: ⊤ ∈ OpenSets
  open_sUnion (U: Set (Set α)) (hU: U ⊆ OpenSets) : ⋃ U ∈ OpenSets
  open_inter (a b: Set α) (ha: a ∈ OpenSets) (hb: b ∈ OpenSets) : a ∩ b ∈ OpenSets

public class TopologicalSpace (α: Type*) where
  toTopology: Topology α := by exact inferInstance

namespace Topology

public instance : LE (Topology α) where
  le a b := b.OpenSets ⊆ a.OpenSets
public instance : LT (Topology α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

public instance : IsPartialOrder (Topology α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl _ := Set.sub_refl _
  htrans h g := le_trans (α := Set (Set α)) g h
  antisymm {t s} h g := by
    ext; apply Iff.intro
    apply g; apply h

inductive Generate (U: Set (Set α)) : Set α -> Prop where
| of (u: Set α) : u ∈ U -> Generate U u
| top : Generate U ⊤
| sUnion (V: Set (Set α)) : V ⊆ Set.mk (Generate U) -> Generate U (⋃ V)
| inter (a b: Set α) : Generate U a -> Generate U b -> Generate U (a ∩ b)

public def generate (U: Set (Set α)) : Topology α where
  OpenSets := Set.mk (Generate U)
  open_top := Generate.top
  open_sUnion := Generate.sUnion
  open_inter := Generate.inter

public theorem generate_of (U: Set (Set α)) : U ⊆ (generate U).OpenSets := Generate.of

public theorem of_generate_map (U: Set (Set β)) (ta: Topology α) :
  ∀{s}, s ∈ (generate U).OpenSets ->
  ∀(f: α -> β), (∀u ∈ U, u.preimage f ∈ ta.OpenSets) ->
  s.preimage f ∈ ta.OpenSets := by
  intro s hs f hf
  induction hs with
  | of => apply hf; assumption
  | top => apply open_top
  | sUnion _ _ ih =>
    rw [Set.sUnion_preimage]; apply open_sUnion
    rintro _ ⟨x, hx, rfl⟩
    apply ih; assumption
  | inter =>
    rw [Set.inter_preimage]
    apply open_inter <;> assumption

public theorem of_generate (U: Set (Set α)) (t: Topology α) (h: U ⊆ t.OpenSets) : t ≤ generate U := by
  intro x hx; induction hx with
  | of => apply h; assumption
  | top => apply open_top
  | sUnion => apply open_sUnion; assumption
  | inter => apply open_inter <;> assumption

public def gci : GaloisCoinsertion (α := Topology α) (β := (Set (Set α))ᵒᵖ) (fun t => .mk t.OpenSets) (fun s => generate s.get) where
  gc := by
    intro t U; dsimp
    apply Iff.intro
    intro h
    apply of_generate
    assumption
    intro h
    intro x hx; apply h
    apply generate_of
    assumption
  u_l_le U := by
    intro x
    intro hx; apply generate_of
    assumption
  choice x hx := {
    OpenSets := x.get
    open_top := by
      apply hx
      apply Generate.top
    open_sUnion U hU := by
      apply hx
      apply Generate.sUnion _ (Set.sub_trans hU _)
      apply generate_of
    open_inter := by
      intro a b ha hb; apply hx
      apply Generate.inter
      apply generate_of; assumption
      apply generate_of; assumption
  }
  choice_eq x hx := by
    ext s; dsimp
    apply Iff.intro
    apply generate_of
    apply hx

public theorem open_bot (t: Topology α) : ⊥ ∈ t.OpenSets := by
  rw [←Set.sUnion_empty]; apply open_sUnion
  apply Set.empty_sub

public instance : GaloisConnection.CompleteLattice (Topology α) :=
  gci.dual.instCompleteLattice.dual

public theorem of_mem_top [LEM] {s: Set α} : s ∈ (⊤: Topology α).OpenSets -> s ∈ ({⊤, ⊥}: Set (Set α)) := by
  intro hs; induction hs with
  | of u hu => contradiction
  | top => left; rfl
  | inter a b _ _ ha hb =>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl
    all_goals simp
  | sUnion U hU ih =>
    rcases em (⊤ ∈ U) with h | h
    · rw [show ⋃ U = ⊤ from ?_]
      left; rfl
      ext; simp; exists ⊤
    · rw [show ⋃ U = ⊥ from ?_]
      right; rfl
      ext; simp; intro s hs
      rcases ih s hs with h | h
      subst h; contradiction
      subst s; nofun

public class IsContinuous (ta: Topology α) (tb: Topology β) (f: α -> β) where
  isOpen_preimage : ∀s: Set β, s ∈ tb.OpenSets -> s.preimage f ∈ ta.OpenSets

public theorem open_preimage (ta: Topology α) (tb: Topology β) (f: α -> β) [IsContinuous ta tb f] {s: Set β} (hs: s ∈ tb.OpenSets) : s.preimage f ∈ ta.OpenSets :=
  IsContinuous.isOpen_preimage s hs

public theorem IsContinuous.comp (f: β -> γ) (g: α -> β) (c₉: IsContinuous u v f) (c₁: IsContinuous t u g) : IsContinuous t v (f ∘ g) where
  isOpen_preimage s hs := by
    show Set.preimage g (Set.preimage f s) ∈ _
    apply open_preimage t u g
    apply open_preimage u v f
    assumption

public instance cont_from_top : IsContinuous ⊥ t f where
  isOpen_preimage := by intros; trivial
public instance cont_to_bot : IsContinuous t ⊤ f where
  isOpen_preimage := by
    intro s hs
    induction hs with
    | of => contradiction
    | top => apply open_top
    | sUnion _ _ ih =>
      rw [Set.sUnion_preimage]
      apply open_sUnion
      rintro _ ⟨x, hx, rfl⟩
      apply ih
      assumption
    | inter a b _ _ iha ihb =>
      rw [Set.inter_preimage]
      apply open_inter
      assumption
      assumption

@[expose] public def induced (f: α -> β) (tb: Topology β) : Topology α where
  OpenSets := tb.OpenSets.image (Set.preimage f)
  open_top := by
    exists ⊤; apply And.intro
    apply open_top; rfl
  open_inter a b ha hb := by
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exists a ∩ b
    apply And.intro
    apply open_inter <;> assumption
    rw [Set.inter_preimage]
  open_sUnion U hU := by
    let V : Set (Set β) := {
      Mem v := ∃x ∈ U, v ∈ tb.OpenSets ∧ v.preimage f = x
    }
    exists ⋃ V
    apply And.intro
    · apply open_sUnion
      rintro t ⟨_, pret_in_u, open_t, rfl⟩
      assumption
    · ext a; apply Iff.intro
      · intro ⟨s, ⟨_, pres_in_u, s_in_tb, rfl⟩, fa_in_s⟩
        exists s.preimage f
      · intro ⟨s, s_in_u, a_in_s⟩
        obtain ⟨t, open_t, rfl⟩ := hU s s_in_u
        exists t; apply And.intro
        exact ⟨t.preimage f, s_in_u, open_t, rfl⟩
        assumption

@[expose] public def coinduced (f: α -> β) (ta: Topology α) : Topology β where
  OpenSets := ta.OpenSets.preimage (·.preimage f)
  open_top := by apply open_top
  open_inter a b ha hb := by
    rw [Set.mem_preimage, Set.inter_preimage]
    apply open_inter <;> assumption
  open_sUnion U hU := by
    rw [Set.mem_preimage, Set.sUnion_preimage]
    apply open_sUnion
    rintro _ ⟨s, s_in_U, rfl⟩
    apply hU; assumption

instance cont_from_induced (tb: Topology β) (f: α -> β) : IsContinuous (tb.induced f) tb f where
  isOpen_preimage s hs := by exists s
instance cont_to_coinduced (ta: Topology α) (f: α -> β) : IsContinuous ta (ta.coinduced f) f where
  isOpen_preimage _ hs := hs

public theorem cont_le_src (ta ta': Topology α) {tb: Topology β} {f: α -> β} (h: IsContinuous ta tb f) (h: ta' ≤ ta) : IsContinuous ta' tb f where
  isOpen_preimage s hs := by apply h; apply open_preimage ta tb; assumption
public theorem cont_dst_le {ta: Topology α} (tb tb': Topology β) {f: α -> β} (h: IsContinuous ta tb f) (h: tb ≤ tb') : IsContinuous ta tb' f where
  isOpen_preimage s hs := by
    apply open_preimage ta tb
    apply h; assumption

section

variable (ta: Topology α) (tb: Topology β)
  {ι : Type*} {Y : ι → Type*} (t:  ∀i: ι, Topology (Y i))

public instance cont_id : IsContinuous ta ta id where
  isOpen_preimage _ hs := hs

@[expose] public def prod : Topology (α × β) :=
  (ta.induced Prod.fst) ⊓ (tb.induced Prod.snd)

@[expose] public def sum : Topology (α ⊕ β) :=
  (ta.coinduced Sum.inl) ⊔ (tb.coinduced Sum.inr)

@[expose] public def pi : Topology (∀i: ι, Y i) :=
  ⨅i, induced (fun f => f i) (t i)

@[expose] public def sigma : Topology (Σi: ι, Y i) :=
  ⨆i, coinduced (Sigma.mk i) (t i)

public instance cont_prod_fst : IsContinuous (ta.prod tb) ta Prod.fst := by
  apply cont_le_src (ta.induced Prod.fst)
  infer_instance
  apply min_le_left

public instance cont_prod_snd : IsContinuous (ta.prod tb) tb Prod.snd := by
  apply cont_le_src (tb.induced Prod.snd)
  infer_instance
  apply min_le_right

public instance cont_sum_inl : IsContinuous ta (ta.sum tb) Sum.inl := by
  apply cont_dst_le (ta.coinduced Sum.inl)
  infer_instance
  apply left_le_max

public instance cont_sum_inr : IsContinuous tb (ta.sum tb) Sum.inr := by
  apply cont_dst_le (tb.coinduced Sum.inr)
  infer_instance
  apply right_le_max

public instance cont_pi_apply : IsContinuous (pi t) (t i) (fun f => f i) := by
  apply cont_le_src ((t i).induced (fun f => f i))
  infer_instance
  apply sInf_le
  apply Set.mem_range'

public instance cont_sigma_mk : IsContinuous (t i) (sigma t) (Sigma.mk i) := by
  apply cont_dst_le ((t i).coinduced (Sigma.mk i))
  infer_instance
  apply le_sSup
  apply Set.mem_range'

end

public structure TopologyEquiv (ta: Topology α) (tb: Topology β) extends α ≃ β where
  toFun_continuous : IsContinuous ta tb toFun
  invFun_continuous : IsContinuous tb ta invFun

infixr:50 " ≃ᵗ " => TopologyEquiv

namespace TopologyEquiv

public instance {ta: Topology α} {tb: Topology β} : EquivLike (ta ≃ᵗ tb) α β where

@[expose] public def id (ta: Topology α) : ta ≃ᵗ ta where
  toEquiv := .id _
  toFun_continuous := cont_id _
  invFun_continuous := cont_id _

variable {ta: Topology α} {tb: Topology β} {tc: Topology γ}

@[expose] public def symm (f: TopologyEquiv ta tb) : tb ≃ᵗ ta where
  toEquiv := f.toEquiv.symm
  toFun_continuous := f.invFun_continuous
  invFun_continuous := f.toFun_continuous

@[expose] public def trans (f: ta ≃ᵗ tb) (g: tb ≃ᵗ tc) : ta ≃ᵗ tc where
  toEquiv := f.toEquiv.trans g.toEquiv
  toFun_continuous := by
    apply IsContinuous.comp g f
    exact g.toFun_continuous
    exact f.toFun_continuous
  invFun_continuous := by
    apply IsContinuous.comp f.symm g.symm
    exact f.invFun_continuous
    exact g.invFun_continuous

variable {ta: Topology α} {tb: Topology β}

@[ext] theorem ext (a b: ta ≃ᵗ tb) (h: ∀i, a i = b i) : a = b := DFunlike.ext _ _ h
@[simp] theorem apply_id (ta: Topology α) (x: α) : TopologyEquiv.id ta x = x := rfl
@[simp] theorem apply_comp (f: tb ≃ᵗ tc) (g: ta ≃ᵗ tb) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] theorem apply_trans (f: tb ≃ᵗ tc) (g: ta ≃ᵗ tb) (x: α) : (g.trans f) x = f (g x) := rfl

@[simp] theorem symm_apply (f: ta ≃ᵗ tb) (x: β) : f (f.symm x) = x := f.toEquiv.symm_apply _
@[simp] theorem apply_symm (f: ta ≃ᵗ tb) (x: α) : f.symm (f x) = x := f.toEquiv.apply_symm _

@[simp] theorem symm_symm (f: ta ≃ᵗ tb) : f.symm.symm = f := rfl

@[simp] theorem trans_assoc (f: ta ≃ᵗ tb) (g: tb ≃ᵗ tc) (h: tc ≃ᵗ tc') :
  f.trans (g.trans h) = (f.trans g).trans h := rfl

@[simp] theorem symm_trans (f: ta ≃ᵗ tb) : f.symm.trans f = .id _ := by
  ext x; simp
@[simp] theorem trans_symm (f: ta ≃ᵗ tb) : f.trans f.symm = .id _ := by
  ext x; simp
@[simp] theorem id_symm : (TopologyEquiv.id _).symm = (TopologyEquiv.id ta) := rfl
@[simp] theorem id_trans (f: ta ≃ᵗ tb) : (TopologyEquiv.id _).trans f = f := rfl
@[simp] theorem trans_id (f: ta ≃ᵗ tb) : f.trans (TopologyEquiv.id _) = f := rfl

public theorem inj (f: ta ≃ᵗ tb) : Function.Injective f := f.rightInv.injective
public theorem surj (f: ta ≃ᵗ tb) : Function.Surjective f := f.symm.rightInv.surjective

end TopologyEquiv

end Topology

namespace TopologicalSpace

@[expose] public def IsOpen (α: Type*) [TopologicalSpace α] : Set α -> Prop :=
  (· ∈ toTopology.OpenSets)

variable [TopologicalSpace α] [TopologicalSpace β]

public theorem open_top : IsOpen α ⊤ := Topology.open_top _
public theorem open_bot : IsOpen α ⊥ := Topology.open_bot _
public theorem open_inter : IsOpen α a -> IsOpen α b -> IsOpen α (a ∩ b) := Topology.open_inter _ _ _
public theorem open_sUnion {U: Set (Set α)} : (∀u ∈ U, IsOpen α u) -> IsOpen α (⋃ U) := Topology.open_sUnion _ _

public abbrev IsContinuous {α β: Type*} [TopologicalSpace α] [TopologicalSpace β] (f: α -> β) :=
  Topology.IsContinuous toTopology toTopology f

public theorem open_preimage (f: α -> β) [IsContinuous f] {s: Set β} (hs: IsOpen β s) : IsOpen α (s.preimage f) :=
  Topology.open_preimage _ _ _ hs

-- endow these structures with the discrete topology
public instance : TopologicalSpace ℕ := ⟨⊥⟩
public instance : TopologicalSpace ℤ := ⟨⊥⟩
public instance : TopologicalSpace Bool := ⟨⊥⟩
public instance (n: ℕ) : TopologicalSpace (Fin n) := ⟨⊥⟩

section

variable [TopologicalSpace α] [TopologicalSpace β]
  {ι : Type*} {γ : ι → Type*} [∀i: ι, TopologicalSpace (γ i)]

public instance : IsContinuous (@id α) :=
  Topology.cont_id _
public instance : IsContinuous (fun x: α => x) :=
  Topology.cont_id _

public instance : TopologicalSpace (α × β) :=
  ⟨Topology.prod toTopology toTopology⟩
public instance : TopologicalSpace (α ⊕ β) :=
  ⟨Topology.sum toTopology toTopology⟩
public instance : TopologicalSpace (∀i, γ i) :=
  ⟨Topology.pi (fun _ => toTopology)⟩
public instance : TopologicalSpace (Σi, γ i) :=
  ⟨Topology.sigma (fun _ => toTopology)⟩

public instance : IsContinuous (Prod.fst: α × β -> α) :=
  Topology.cont_prod_fst _ _
public instance : IsContinuous (Prod.snd: α × β -> β) :=
  Topology.cont_prod_snd _ _
public instance : IsContinuous (Sum.inl: α -> α ⊕ β) :=
  Topology.cont_sum_inl _ _
public instance : IsContinuous (Sum.inr: β -> α ⊕ β) :=
  Topology.cont_sum_inr _ _
public instance : IsContinuous (fun f: (∀i, γ i) => f i) :=
  Topology.cont_pi_apply _
public instance : IsContinuous (Sigma.mk i: γ i -> Sigma γ) :=
  Topology.cont_sigma_mk (fun _ => toTopology)

end

end TopologicalSpace

open TopologicalSpace

@[expose] public def TopologyEquiv (α β: Type*) [TopologicalSpace α] [TopologicalSpace β] :=
  (toTopology: Topology α) ≃ᵗ (toTopology: Topology β)

infixr:50 " ≃ₜ " => TopologyEquiv

namespace TopologyEquiv

variable {α β γ y': Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace γ']

public instance : EquivLike (α ≃ₜ β) α β :=
  Topology.TopologyEquiv.instEquivLike
    (α := α) (β := β)
    (ta := toTopology) (tb := toTopology)

@[expose] public def id (α: Type*) [TopologicalSpace α] : α ≃ₜ α :=
  Topology.TopologyEquiv.id _

@[expose] public def symm : α ≃ₜ β -> β ≃ₜ α :=
  Topology.TopologyEquiv.symm

@[expose] public def trans : α ≃ₜ β -> β ≃ₜ γ -> α ≃ₜ γ :=
  Topology.TopologyEquiv.trans

@[ext] theorem ext (a b: α ≃ₜ β) (h: ∀i, a i = b i) : a = b := DFunlike.ext _ _ h
@[simp] theorem apply_id (x: α) : TopologyEquiv.id α x = x := rfl
@[simp] theorem apply_comp (f: β ≃ₜ γ) (g: α ≃ₜ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] theorem apply_trans (f: β ≃ₜ γ) (g: α ≃ₜ β) (x: α) : (g.trans f) x = f (g x) := rfl

@[simp] theorem symm_apply (f: α ≃ₜ β) (x: β) : f (f.symm x) = x := f.toEquiv.symm_apply _
@[simp] theorem apply_symm (f: α ≃ₜ β) (x: α) : f.symm (f x) = x := f.toEquiv.apply_symm _

@[simp] theorem symm_symm (f: α ≃ₜ β) : f.symm.symm = f := rfl

@[simp] theorem trans_assoc (f: α ≃ₜ β) (g: β ≃ₜ γ) (h: γ ≃ₜ γ') :
  f.trans (g.trans h) = (f.trans g).trans h := rfl

@[simp] theorem symm_trans (f: α ≃ₜ β) : f.symm.trans f = .id _ := by
  ext x; simp
@[simp] theorem trans_symm (f: α ≃ₜ β) : f.trans f.symm = .id _ := by
  ext x; simp
@[simp] theorem id_symm : (TopologyEquiv.id _).symm = (TopologyEquiv.id α) := rfl
@[simp] theorem id_trans (f: α ≃ₜ β) : (TopologyEquiv.id _).trans f = f := rfl
@[simp] theorem trans_id (f: α ≃ₜ β) : f.trans (TopologyEquiv.id _) = f := rfl

public theorem inj (f: α ≃ₜ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃ₜ β) : Function.Surjective f := f.symm.rightInv.surjective

end TopologyEquiv
