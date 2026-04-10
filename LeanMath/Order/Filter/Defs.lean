import LeanMath.Order.GaloisConnection
import LeanMath.Data.Set.Defs
import LeanMath.Order.Basic

class IsFilter (F: Type*) (α: Type*) [Membership α F] [LE α] [Min α] where
  protected mem_min (f: F) {a b: α}: a ∈ f -> b ∈ f -> a ⊓ b ∈ f := by intro f; exact f.mem_min
  protected mem_ge (f: F) {a: α} : a ∈ f -> ∀{b}, a ≤ b -> b ∈ f := by intro f; exact f.mem_ge

def mem_min [Membership α F] [LE α] [Min α] [IsFilter F α] (f: F) {a b: α}: a ∈ f -> b ∈ f -> a ⊓ b ∈ f := IsFilter.mem_min _
def mem_ge [Membership α F] [LE α] [Min α] [IsFilter F α] (f: F) {a: α} : a ∈ f -> ∀{b}, a ≤ b -> b ∈ f := IsFilter.mem_ge _

@[ext]
structure Order.Prefilter (α: Type*) [LE α] [Min α] where
  toSet: Set α
  protected mem_min {a b: α}: a ∈ toSet -> b ∈ toSet -> a ⊓ b ∈ toSet
  protected mem_ge {a: α} : a ∈ toSet -> ∀{b}, a ≤ b -> b ∈ toSet

@[ext]
structure Order.Filter (α: Type*) [LE α] [Min α] extends Order.Prefilter α where
  protected nonempty : toSet.Nonempty

namespace Order.Prefilter

instance [LE α] [Min α] : Membership α (Prefilter α) where
  mem f a := a ∈ f.toSet

instance [LE α] [Min α] : IsFilter (Prefilter α) α where

def copy [LE α] [Min α] (f: Prefilter α) (U: Set α) (hx: ∀x, x ∈ f ↔ x ∈ U) : Prefilter α where
  toSet := U
  mem_min {a b} ha hb := by
    apply (hx _).mp
    apply mem_min f
    apply (hx _).mpr
    assumption
    apply (hx _).mpr
    assumption
  mem_ge {a} ha {b} hb := by
    apply (hx _).mp
    apply mem_ge f
    apply (hx _).mpr
    assumption
    assumption

inductive Generate {α: Type*} [LE α] [Min α] (U: Set α) : α -> Prop where
| of (a: α) (ha: a ∈ U) : Generate U a
| min {a b: α} : Generate U a -> Generate U b -> Generate U (a ⊓ b)
| ge {a: α} : Generate U a -> ∀{b}, a ≤ b -> Generate U b

def generate [LE α] [Min α] (U: Set α) : Prefilter α where
  toSet := Set.ofMem (Generate U)
  mem_min := Generate.min
  mem_ge := Generate.ge

def generate_of [LE α] [Min α] (U: Set α) : ∀x ∈ U, x ∈ generate U := Generate.of

def of_mem_generate [LE α] [Min α] (U: Set α) (f: Prefilter α) (h: ∀x ∈ U, x ∈ f) : ∀x ∈ generate U, x ∈ f := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | min => apply mem_min <;> assumption
  | ge => apply mem_ge <;> assumption

def mem_generate_iff [LE α] [LT α] [Min α] [IsSemiLatticeMin α] {U: Set α} : ∀{x}, x ∈ generate U ↔ ∃(as: List α) (has: as ≠ []), Set.ofList as ⊆ U ∧ as.min has ≤ x := by
  intro x; apply Iff.intro
  · intro h
    induction h with
    | of a ha =>
      refine ⟨[a], nofun, ?_, ?_⟩
      · intro x hx; cases hx
        assumption
        contradiction
      · rfl
    | min x y hx hy =>
      obtain ⟨as, has, as_sub, as_eq⟩ := hx
      obtain ⟨bs, hbs, bs_sub, bs_eq⟩ := hy
      refine ⟨as ++ bs, ?_, ?_, ?_⟩
      · intro h
        rw [List.append_eq_nil_iff] at h
        cases h; contradiction
      · intro x hx
        simp at hx

        rcases hx with hx | hx
        · apply as_sub; assumption
        · apply bs_sub; assumption
      · rw [List.min_append as bs has hbs]
        apply min_le_min
        assumption
        assumption
    | @ge a ha b hb ih =>
      obtain ⟨as, has, sub, le⟩ := ih
      refine ⟨as, has, sub, ?_⟩
      apply le_trans le
      assumption
  · intro ⟨as, has, sub, le⟩
    apply Generate.ge _ le
    show Generate U (as.min has)
    clear le
    cases as with
    | nil => contradiction
    | cons a as =>
    unfold List.min; dsimp
    clear has
    have ha : Generate U a := by
      apply generate_of
      apply sub; left
    replace sub : Set.ofList as ⊆ U := by
      intro x hx
      apply sub
      right; assumption
    induction as generalizing a with
    | nil => assumption
    | cons a' as ih =>
      rw [List.foldl_cons]
      apply ih
      apply Generate.min
      assumption
      apply generate_of
      apply sub; left
      intro x hx
      apply sub; right; assumption

instance [LE α] [Min α] : LE (Prefilter α) where
  le B C := ∀x ∈ C, x ∈ B
instance [LE α] [Min α] : LT (Prefilter α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

section

attribute [local irreducible] OrderOpp in
def gi (α: Type*) [LE α] [Min α] : GaloisInsertion (α := Set α) (β := (Prefilter α)ᵒᵖ) (OrderOpp.mk ∘ generate) (toSet ∘ OrderOpp.get) where
  gc := by
    intro a b
    cases b with | _ b =>
    dsimp; show b ≤ generate a ↔ _
    apply Iff.intro
    · intro h
      intro x hx
      exact h x (generate_of _ _ hx)
    · intro h x hx
      apply of_mem_generate a
      exact h
      assumption
  le_l_u := by
    intro f; cases f with | _ f =>
    dsimp; show generate f.toSet ≤ f
    intro x hx
    apply of_mem_generate
    apply generate_of
    apply generate_of
    assumption
  choice U hU := OrderOpp.mk {
    toSet := U
    mem_min {a b} ha hb := hU _ (Generate.min (Generate.of _ ha) (Generate.of _ hb))
    mem_ge {a} ha {b} hb := hU _ (Generate.ge (Generate.of _ ha) hb)
  }
  choice_eq := by
    intro x hx
    dsimp; congr
    ext a; apply Iff.intro; apply Generate.of
    intro h
    apply hx
    assumption

instance [LE α] [Min α] : IsPartialOrder (Prefilter α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl a _ := id
  trans f g _ h := f _ (g _ h)
  antisymm f g := by
    ext; apply Iff.intro
    apply g; apply f

@[reducible]
local instance lattice (α: Type*) [LE α] [Min α] : GaloisConnection.CompleteLattice (Prefilter α)ᵒᵖ := {
  (gi α).liftCompleteLattice with
  bot := OrderOpp.mk {
    toSet := ⊥
    mem_min := nofun
    mem_ge := nofun
  }
  bot_le := nofun
}

variable [LE α] [Min α]

instance : Top (Prefilter α) := (inferInstance: (Top (Prefilter α)ᵒᵖᵒᵖ))
instance : Bot (Prefilter α) := (inferInstance: (Bot (Prefilter α)ᵒᵖᵒᵖ))
instance : Min (Prefilter α) := (inferInstance: (Min (Prefilter α)ᵒᵖᵒᵖ))
instance : Max (Prefilter α) := (inferInstance: (Max (Prefilter α)ᵒᵖᵒᵖ))
instance : SupSet (Prefilter α) := (inferInstance: (SupSet (Prefilter α)ᵒᵖᵒᵖ))
instance : InfSet (Prefilter α) := (inferInstance: (InfSet (Prefilter α)ᵒᵖᵒᵖ))
instance : IsCompleteLattice (Prefilter α) :=
  (lattice α).toIsCompleteLattice.opp

example : (⊤: Prefilter α).toSet = ⊥ := rfl
example : (⊥: Prefilter α).toSet = ⊤ := rfl

end

end Order.Prefilter

namespace Order.Filter

instance [LE α] [Min α] : Membership α (Filter α) where
  mem f a := a ∈ f.toSet

instance [LE α] [Min α] : IsFilter (Filter α) α where

def copy [LE α] [Min α] (f: Filter α) (U: Set α) (hx: ∀x, x ∈ f ↔ x ∈ U) : Filter α where
  toPrefilter := f.toPrefilter.copy U hx
  nonempty := by
    have ⟨x, h⟩ := f.nonempty
    exists x; exact (hx _).mp h

section

variable [LE α] [Min α]

instance : LE (Filter α) where
  le B C := ∀x ∈ C, x ∈ B
instance : LT (Filter α) where
  lt a b := a ≤ b ∧ ¬b ≤ a

def orderHomPrefilter : Filter α ↪o Prefilter α where
  toFun := toPrefilter
  map_rel := Iff.rfl
  inj := by
    intro a b h
    cases a; congr

instance : IsLawfulLT (Filter α) where
  lt_iff_le_and_not_ge := Iff.rfl
instance : IsPartialOrder (Filter α) where
  refl _ := le_refl (α := Prefilter α) _
  trans := le_trans (α := Prefilter α)
  antisymm {a b} h g := by
    apply inj orderHomPrefilter
    apply le_antisymm <;> assumption

instance : Min (Filter α) where
  min a b := {
    toPrefilter := a.toPrefilter ⊓ b.toPrefilter
    nonempty := by
      show (Prefilter.generate (a.toSet ⊔ b.toSet)).toSet.Nonempty
      have ⟨x, hx⟩ := a.nonempty
      exists x
      apply Prefilter.generate_of
      left; assumption
  }

instance [Max α] [IsLawfulMax α] : Max (Filter α) where
  max a b := {
    toPrefilter := a.toPrefilter ⊔ b.toPrefilter
    nonempty := by
      show (a.toSet ⊓ b.toSet).Nonempty
      have ⟨x, hx⟩ := a.nonempty
      have ⟨y, hy⟩ := b.nonempty
      exists x ⊔ y
      apply And.intro
      apply mem_ge a
      assumption; apply left_le_max
      apply mem_ge b
      assumption; apply right_le_max
  }

instance : IsSemiLatticeMin (Filter α) where
  min_le_left := min_le_left (α := Prefilter α)
  min_le_right := min_le_right (α := Prefilter α)
  le_min := le_min (α := Prefilter α)
instance [Max α] [IsLawfulMax α] : IsLattice (Filter α) where
  left_le_max := left_le_max (α := Prefilter α)
  right_le_max := right_le_max (α := Prefilter α)
  max_le := max_le (α := Prefilter α)

end

section

variable [LE α] [LT α] [Min α] [IsSemiLatticeMin α]

def principal (a: α) : Filter α where
  toSet := Set.Ici a
  nonempty := ⟨a, le_refl _⟩
  mem_min {_ _} hx hy := le_min hx hy
  mem_ge {_} hx {_} hy := le_trans hx hy

scoped notation "𝓟" => Filter.principal

@[simp] def mem_principal {s t : α} : s ∈ 𝓟 t ↔ t ≤ s := Iff.rfl

def mem_principal_self (s : α) : s ∈ 𝓟 s := le_refl _

def principal_le_principal {s t: α} : s ≤ t ↔ 𝓟 s ≤ 𝓟 t := by
  apply Iff.intro
  · intro t_le_s x hx
    rw [mem_principal] at *
    apply le_trans
    assumption
    assumption
  · intro h; apply h
    apply mem_principal_self

def le_principal_iff {s: α} : f ≤ 𝓟 s ↔ s ∈ f := by
  apply Iff.intro
  intro h
  apply h
  apply mem_principal_self
  intro h x hx
  have := mem_principal.mp hx
  apply mem_ge
  assumption
  assumption

end

section

variable [LE α] [LT α] [Min α] [Top α] [IsLawfulTop α] [IsSemiLatticeMin α]

def mem_top (f: Filter α) : ⊤ ∈ f := by
  have ⟨x, hx⟩ := f.nonempty
  apply mem_ge
  assumption
  apply le_top

instance : Top (Filter α) where
  top := {
    toSet := {⊤}
    nonempty := ⟨⊤, Set.mem_singleton.mp rfl⟩
    mem_min := by
      intro x y rfl rfl
      apply le_antisymm
      apply le_min
      repeat apply le_top
    mem_ge := by
      intro x y _ _; subst x
      apply le_antisymm
      assumption; apply le_top
  }

instance : IsLawfulTop (Filter α) where
  le_top a := by intro _ rfl; apply mem_top

instance : Bot (Filter α) where
  bot := {
    toSet := ⊤
    nonempty := ⟨⊤, True.intro⟩
    mem_min _ _ := True.intro
    mem_ge _ _ _ := True.intro
  }

instance : IsLawfulBot (Filter α) where
  bot_le _ _ _ := True.intro

def generate (U: Set α) : Filter α where
  toPrefilter := Prefilter.generate (insert ⊤ U)
  nonempty := by
    exists ⊤
    apply Prefilter.generate_of
    left; rfl

def generate_of (U: Set α) : ∀x ∈ U, x ∈ generate U := by
  intro x hx
  apply Prefilter.generate_of
  right; assumption

def of_mem_generate (U: Set α) (f: Filter α) (h: ∀x ∈ U, x ∈ f) : ∀x ∈ generate U, x ∈ f := by
  intro x hx
  induction hx with
  | of x hx =>
    rcases hx with rfl | hx
    apply mem_top
    apply h
    assumption
  | min => apply mem_min <;> assumption
  | ge => apply mem_ge <;> assumption

def mem_generate_iff {U: Set α} : ∀{x}, x ∈ generate U ↔ ∃as: List α, Set.ofList as ⊆ U ∧ (⊤::as).min nofun ≤ x := by
  intro x; apply Iff.trans Prefilter.mem_generate_iff
  apply Iff.intro
  ·
    intro ⟨as, has, sub, le⟩
    suffices ∃bs: List α, Set.ofList bs ⊆ U ∧ (⊤::bs).min nofun ≤ as.min has by
      obtain ⟨bs, hbs, le'⟩ := this
      exists bs; apply And.intro hbs
      apply le_trans le'
      assumption
    clear le x
    induction as with
    | nil => contradiction
    | cons a as ih =>
      show ∃_, _ ∧ _ ≤ List.min (a::as) nofun
      clear has
      rcases em (as = []) with h | h
      · subst as
        have := sub a (by simp)
        rcases this with rfl | ha
        · exists []; apply And.intro
          nofun; rfl
        · exists [a]; apply And.intro
          intro x; simp; intro rfl; assumption
          simp; rw [min_eq_right]
          apply le_top
      · have ⟨bs, hbs, bs_le⟩ := ih h ?_
        have := sub a (by simp)
        rcases this with rfl | ha
        · exists bs; apply And.intro
          assumption;
          rw [List.min_cons'' _ _ h]
          rw [min_eq_right]
          assumption
          apply le_top
        · exists a::bs; apply And.intro
          intro x; simp
          intro h; rcases h with rfl | h
          assumption
          apply hbs; assumption
          rw [List.min_eq_of_perm _ _ (List.Perm.swap _ _ _),
            List.min_cons', List.min_cons'' _ _ h]
          apply min_le_min (le_refl _)
          assumption
        · apply Set.sub_trans _ sub
          intro x hx; right; assumption
  · intro ⟨as, sub, le⟩
    cases as with
    | nil =>
      refine ⟨[⊤], nofun, ?_, ?_⟩
      intro x hx
      cases List.mem_singleton.mp hx
      left; rfl
      assumption
    | cons a as =>
      refine ⟨a::as, nofun, ?_, ?_⟩
      apply Set.sub_trans sub
      intro x hx; right; assumption
      apply le_trans _ le
      rw [List.min_cons']
      rw [min_eq_right]
      apply le_top

def ofPrefilter (f: Prefilter α) : Filter α where
  toSet := insert ⊤ f.toSet
  nonempty := ⟨_, .inl rfl⟩
  mem_min := by
    intro a b ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    left; rw [min_eq_right]; rfl; rfl
    right; rwa [min_eq_right]
    apply le_top; rw [min_eq_left]
    right; assumption; apply le_top
    right; apply mem_min f <;> assumption
  mem_ge := by
    intro a ha b hb
    rcases ha with rfl | ha
    left; apply le_antisymm
    assumption; apply le_top
    right; apply mem_ge f
    assumption; assumption

attribute [local irreducible] OrderOpp in
def gi (α: Type*) [LE α] [LT α] [Min α] [Top α] [IsLawfulTop α] [IsSemiLatticeMin α] : GaloisInsertion (α := (Prefilter α)ᵒᵖ) (β := (Filter α)ᵒᵖ) (OrderOpp.mk ∘ ofPrefilter ∘ OrderOpp.get) (OrderOpp.mk ∘ toPrefilter ∘ OrderOpp.get) :=
  GaloisCoinsertion.dual {
    gc := by
      intro a b
      apply Iff.intro
      intro h
      intro x hx
      rcases hx with rfl | hx
      apply mem_top; apply h; assumption
      intro h x hx
      apply h
      right; assumption
    u_l_le := by
      intro f a ha
      right; assumption
    choice x hx := {
      toPrefilter := x
      nonempty := ⟨_, hx ⊤ (mem_top _)⟩
    }
    choice_eq := by
      intro a ha
      ext x; simp [ofPrefilter]
      intro rfl;
      apply ha; apply mem_top
  }

instance : SupSet (Filter α) where
  sSup U := {
    toSet := { Mem x := ∀f ∈ U, x ∈ f }
    nonempty := ⟨⊤, fun f _ => mem_top _⟩
    mem_min := by
      intro a b ha hb f hf
      apply mem_min
      apply ha
      assumption
      apply hb
      assumption
    mem_ge := by
      intro a ha b hb f hf
      apply mem_ge
      apply ha
      assumption
      assumption
  }

instance : InfSet (Filter α) where
  sInf U := generate (⋃ U.image fun x => x.toSet)

instance : Max (Filter α) where
  max a b := {
    toPrefilter := a.toPrefilter ⊔ b.toPrefilter
    nonempty := by
      show (a.toSet ⊓ b.toSet).Nonempty
      exists ⊤
      apply And.intro
      apply mem_top
      apply mem_top
  }

protected def le_sSup (U: Set (Filter α)) (u: Filter α) (hu: u ∈ U) : u ≤ ⨆ U := by
  intro x hx
  apply hx
  assumption

protected def sSup_le (U: Set (Filter α)) (x: Filter α) : (∀u ∈ U, u ≤ x) -> ⨆ U ≤ x := by
  intro hU a ha f hf
  apply hU
  assumption
  assumption

instance : IsCompleteLattice (Filter α) where
  left_le_max := left_le_max (α := Prefilter α)
  right_le_max := right_le_max (α := Prefilter α)
  max_le := max_le (α := Prefilter α)
  le_sSup := Filter.le_sSup
  sSup_le := Filter.sSup_le
  sInf_le := by
    intro U f hf u hu
    apply generate_of
    exists f.toSet; apply And.intro
    apply Set.mem_image'
    assumption
    assumption
  le_sInf := by
    intro U f hU x hx
    apply of_mem_generate _ _ _ _ hx
    intro y hy
    simp at hy
    obtain ⟨_, ⟨f', hf', rfl⟩, _⟩ := hy
    apply hU
    assumption
    assumption

example : (⊤: Prefilter α).toSet = ⊥ := rfl
example : (⊥: Prefilter α).toSet = ⊤ := rfl

def mem_sSup {U: Set (Filter α)} : ∀{x}, x ∈ sSup U ↔ ∀u ∈ U, x ∈ u := Iff.rfl
def mem_sInf {U: Set (Filter α)} : ∀{x}, x ∈ sInf U ↔
  ∃(as: List α), Set.ofList as ⊆ (⋃ (U.image (fun f => f.toSet))) ∧ (⊤::as).min nofun ≤ x := by
  apply mem_generate_iff

end

section

variable [LE α] [LT α] [Min α] [Top α] [IsLawfulTop α] [IsSemiLatticeMin α]

def join (fs : Filter (Set (Filter α))) : Filter α where
  toSet := { Mem a := (Set.ofMem fun f => a ∈ f) ∈ fs }
  nonempty := by
    exists ⊤; dsimp
    have ⟨U, hU⟩ := fs.nonempty
    rw [show Set.ofMem (fun f: Filter α => ⊤ ∈ f) = ⊤ from ?_]
    apply mem_top
    ext; simp; apply mem_top
  mem_min {a b} ha hb := by
    dsimp at *
    rw [show Set.ofMem (fun f: Filter α => min a b ∈ f) = (
      Set.ofMem (fun f: Filter α => a ∈ f) ⊓ Set.ofMem (fun f: Filter α => b ∈ f)
    ) from ?_]
    apply mem_min <;> assumption
    ext f; simp
    apply Iff.intro
    intro hx; apply And.intro
    dsimp ; apply mem_ge; assumption; apply min_le_left
    dsimp ; apply mem_ge; assumption; apply min_le_right
    intro ⟨ha, hb⟩
    apply mem_min <;> assumption
  mem_ge {a} ha {b} hb := by
    dsimp at *
    apply mem_ge
    assumption
    intro f; dsimp
    intro
    apply mem_ge
    assumption
    assumption

@[simp] def mem_join [Top α] [IsLawfulTop α] {s : α} {f : Filter (Set (Filter α))} : s ∈ join f ↔ (Set.ofMem fun t => s ∈ t) ∈ f := Iff.rfl

def sSup_eq_join_princ (U: Set (Filter α)) : ⨆ U = join (𝓟 U) := by
  apply le_antisymm
  · apply sSup_le
    intro f hf x hx
    rw [mem_join, mem_principal] at hx
    apply hx
    assumption
  · intro x hx
    rw [mem_join, mem_principal]
    intro f hf
    apply hx
    assumption

end

end Order.Filter
