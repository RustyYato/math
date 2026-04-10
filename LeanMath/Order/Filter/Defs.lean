import LeanMath.Order.GaloisConnection
import LeanMath.Data.Set.Defs

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

variable [LE α] [Min α]

end Order.Prefilter

namespace Order.Filter

instance [LE α] [Min α] : Membership α (Filter α) where
  mem f a := a ∈ f.toSet

instance [LE α] [Min α] : IsFilter (Filter α) α where

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

end Order.Filter
