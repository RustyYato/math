import LeanMath.Order.Set
import LeanMath.Data.Set.Relation
import LeanMath.Data.Nat.Find

class IsConditionallyCompleteLattice (α: Type*) [LE α] [LT α] [Min α] [Max α] [InfSet α] [SupSet α] : Prop extends IsLattice α where
  protected le_csSup : ∀{s} {a: α}, s.BoundedAbove → a ∈ s → a ≤ (⨆ s)
  protected csSup_le : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.upperBounds → ⨆ s ≤ a
  protected csInf_le : ∀{s} {a: α}, s.BoundedBelow → a ∈ s → ⨅ s ≤ a
  protected le_csInf : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.lowerBounds → a ≤ ⨅ s

variable [LE α] [LT α] [Min α] [Max α] [InfSet α] [SupSet α] [IsConditionallyCompleteLattice α]

def le_csSup : ∀{s} {a: α}, s.BoundedAbove → a ∈ s → a ≤ (⨆ s) := IsConditionallyCompleteLattice.le_csSup
def csSup_le : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.upperBounds → ⨆ s ≤ a := IsConditionallyCompleteLattice.csSup_le
def csInf_le : ∀{s} {a: α}, s.BoundedBelow → a ∈ s → ⨅ s ≤ a := IsConditionallyCompleteLattice.csInf_le
def le_csInf : ∀{s} {a: α}, Set.Nonempty s → a ∈ s.lowerBounds → a ≤ ⨅ s := IsConditionallyCompleteLattice.le_csInf

instance : IsConditionallyCompleteLattice αᵒᵖ where
  le_csSup := csInf_le (α := α)
  csSup_le := le_csInf (α := α)
  csInf_le := le_csSup (α := α)
  le_csInf := csSup_le (α := α)

def sSup_univ [Top α] [IsLawfulTop α] : ⨆ ⊤ = (⊤: α) := by
  apply le_antisymm (le_top _)
  apply le_csSup
  exists ⊤; intro _ _; apply le_top
  trivial

def sInf_univ [Bot α] [IsLawfulBot α] : ⨅ ⊤ = (⊥: α) :=
  sSup_univ (α := αᵒᵖ)

def csInf_mem [LEM] [IsLinearOrder α] [@Relation.IsWelFounded α (· < ·)]
  {U: Set α} (hU: U.Nonempty) : ⨅ U ∈ U := by
  have : U.BoundedBelow := by
    obtain ⟨x, _⟩ := hU
    have ⟨bot, bot_spec, _⟩ := Relation.exists_unique_min (α := α) (· < ·) (P := fun _ => True) ⟨x, True.intro⟩
    exists bot
    intro x hx
    exact not_lt.mp (bot_spec.right x · True.intro)
  have ⟨u, ⟨umem, hu⟩, _⟩  := Set.exists_unique_min (· < ·) hU
  rwa [show ⨅U = u from ?_]
  apply le_antisymm (csInf_le this umem)
  apply le_csInf
  exists u
  simpa [not_lt] using hu

noncomputable instance [LEM] : SupSet ℕ where
  sSup U :=
    open UniqueChoice in
    if h:U.BoundedAbove then
      Nat.find (P := fun n => n ∈ U.upperBounds) (by
        dsimp; obtain ⟨n, hn⟩ := h
        exists n)
    else
      0

noncomputable instance [LEM] : InfSet ℕ where
  sInf U := sSup U.lowerBounds

def Nat.BoundedBelow (U: Set ℕ) : U.BoundedBelow := by
  exists 0; intro _ _; apply bot_le
def Nat.le_csSup [LEM] : ∀{s} {a: ℕ}, s.BoundedAbove → a ∈ s → a ≤ (⨆ s) := by
  open UniqueChoice in
  intro U u hU hu
  simp [SupSet.sSup]
  rw [dif_pos hU]
  apply Nat.find_spec (P := fun n => n ∈ U.upperBounds) (by
    dsimp; obtain ⟨n, hn⟩ := hU
    exists n)
  assumption
def Nat.csSup_le [LEM] : ∀{s} {a: ℕ}, Set.Nonempty s → a ∈ s.upperBounds → (⨆ s) ≤ a := by
  open UniqueChoice in
  intro U u hU hu
  simp [SupSet.sSup]
  rw [dif_pos ⟨_, hu⟩]
  rw [←not_lt]; intro h
  apply Nat.find_minimal (P := fun n => n ∈ U.upperBounds) (by
    exists u)
  assumption
  assumption

instance [LEM] : IsConditionallyCompleteLattice ℕ where
  le_csSup := Nat.le_csSup
  csSup_le := Nat.csSup_le
  le_csInf := by
    intro U u hU hu
    apply Nat.le_csSup
    obtain ⟨x, hx⟩ := hU
    exists x; intro y hy
    apply hy
    assumption
    assumption
  csInf_le := by
    intro U u hU hu
    apply Nat.csSup_le
    obtain ⟨x, hx⟩ := hU
    exists x; intro y hy
    apply hy
    assumption

def Int.lub_of_ub [LEM] (U: Set ℤ) (h: U.Nonempty) (hU: U.BoundedAbove) : existsUnique fun z => U.IsLUB z := by
  suffices ∃z, Set.IsLUB U z by
    obtain ⟨z, hz⟩ := this
    refine ⟨_, hz, ?_⟩
    intro x hx;
    apply le_antisymm
    apply hz.right
    intro u hu
    apply hx.left
    assumption
    apply hx.right
    intro u hu
    apply hz.left
    assumption
  open UniqueChoice in
  obtain ⟨z, hz⟩ := hU
  obtain ⟨u, hu⟩ := h
  let P (n: ℕ) : Prop := (u + n) ∈ U.upperBounds
  have P_of_ub : ∀z ∈ U.upperBounds, P (z - u).toNat := by
    unfold P; intro z hz v hv
    rw [Int.natCast_toNat_eq_self.mpr]
    rw [Int.add_comm, Int.sub_add_cancel]
    apply hz; assumption
    apply Int.le_sub_right_of_add_le
    rw [Int.zero_add]
    apply hz
    assumption
  have Pexists : ∃n, P n := by
    exists (z - u).toNat
    apply P_of_ub
    assumption
  exists u + Nat.find (P := P) Pexists
  apply And.intro (Nat.find_spec Pexists)
  intro a ha
  rw [←Int.add_zero a, ←Int.sub_self u,
    ←Int.add_sub_assoc, Int.add_comm a, Int.add_sub_assoc,
    ←(Int.natCast_toNat_eq_self (a := a - u)).mpr]
  rw [←not_lt]; intro h
  apply Nat.find_minimal Pexists
  exact Int.ofNat_lt.mp (Int.lt_of_add_lt_add_left h)
  apply P_of_ub
  assumption
  apply Int.le_sub_right_of_add_le
  rw [Int.zero_add]
  apply ha
  assumption

noncomputable instance [LEM] : SupSet ℤ where
  sSup U :=
    open UniqueChoice in
    if h:U.Nonempty ∧ U.BoundedAbove then
      Classical.choose_unique (Int.lub_of_ub U h.left h.right)
    else
      0

noncomputable instance [LEM] : InfSet ℕ where
  sInf U := sSup U.lowerBounds

noncomputable instance [LEM] : InfSet ℤ where
  sInf U := sSup U.lowerBounds

def Int.le_csSup [LEM] : ∀{s} {a: ℤ}, s.BoundedAbove → a ∈ s → a ≤ (⨆ s) := by
  open UniqueChoice in
  intro U u hU hu
  simp [SupSet.sSup]
  rw [dif_pos]
  apply (Classical.choose_unique_spec (Int.lub_of_ub _ _ _)).left
  assumption
  exists u
  assumption
  apply And.intro
  exists u
  assumption

def Int.csSup_le [LEM] : ∀{s} {a: ℤ}, Set.Nonempty s → a ∈ s.upperBounds → (⨆ s) ≤ a := by
  open UniqueChoice in
  intro U u hU hu
  simp [SupSet.sSup]
  rw [dif_pos]
  rw [←not_lt]; intro h
  have lub := Classical.choose_unique_spec (Int.lub_of_ub U hU ⟨_, hu⟩)
  exact not_lt.mpr (lub.right u hu) h
  apply And.intro
  assumption
  exists u

instance [LEM] : IsConditionallyCompleteLattice ℤ where
  le_csSup := Int.le_csSup
  csSup_le := Int.csSup_le
  le_csInf := by
    intro U u hU hu
    apply Int.le_csSup
    obtain ⟨x, hx⟩ := hU
    exists x; intro y hy
    apply hy
    assumption
    assumption
  csInf_le := by
    intro U u hU hu
    apply Int.csSup_le
    obtain ⟨x, hx⟩ := hU
    exists x; intro y hy
    apply hy
    assumption
