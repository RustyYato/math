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

def lt_mem_of_lt_csSup [LEM] [IsLinearOrder α] (U: Set α) (h: Nonempty U) : ∀{a}, a < ⨆ U -> ∃u ∈ U, a < u := by
  intro a ha
  apply LEM.byContradiction; intro g
  simp only [not_exists, not_lt, not_and] at g
  rw [←not_le] at ha; apply ha; clear ha
  apply csSup_le
  assumption
  apply g

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

private def int_natCast_toNat_eq_self {a : ℤ} : ↑a.toNat = a ↔ 0 ≤ a := by
  match a with
  | .ofNat _ =>
    dsimp; apply Iff.intro <;> intro
    apply Int.natCast_nonneg
    rfl
  | .negSucc n =>
    dsimp [Int.toNat]
    apply Iff.intro nofun nofun

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
    rw [int_natCast_toNat_eq_self.mpr]
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
    ←(int_natCast_toNat_eq_self (a := a - u)).mpr]
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

def Int.csSup_mem [LEM] (U: Set ℤ) (h: U.Nonempty) (hU: U.BoundedAbove) : ⨆ U ∈ U := by
  open UniqueChoice in
  obtain ⟨ub, hub⟩ := hU
  have hub' (x: ℤ) (hx: x ∈ U) : 0 ≤ ub - x := by
    apply Int.le_sub_left_of_add_le
    rw [Int.add_zero]; apply hub
    assumption
  let X : Set ℕ := U.image fun z => (ub - z).toNat
  have Xnonempty: X.Nonempty := by
    apply Set.image_nonempty_iff.mpr
    assumption
  replace Xnonempty: ∃x, x ∈ X := by obtain ⟨x, hx⟩ := Xnonempty; exists x
  have ⟨i, hi, eq⟩ := Set.mem_image.mp (Nat.find_spec Xnonempty)
  rw [show ⨆ U = ub - Nat.find Xnonempty from ?_]
  rwa [←eq, Int.toNat_of_nonneg, Int.sub_sub_self]
  apply hub'; assumption
  apply le_antisymm
  · apply csSup_le
    assumption
    intro x hx
    rw [←not_lt]; intro h
    refine Nat.find_minimal Xnonempty (ub - x).toNat ?_ ?_
    apply Int.ofNat_lt.mp
    rwa [Int.toNat_of_nonneg, Int.sub_lt_iff, Int.add_comm, ←Int.sub_lt_iff]
    apply hub'; assumption
    apply Set.mem_image'
    assumption
  · apply le_csSup
    exists ub
    rwa [←eq, Int.toNat_of_nonneg, Int.sub_sub_self]
    apply hub'; assumption

def Int.csInf_mem [LEM] (U: Set ℤ) (h: U.Nonempty) (hU: U.BoundedBelow) : ⨅ U ∈ U := by
  open UniqueChoice in
  obtain ⟨lb, hlb⟩ := hU
  have hlb' (x: ℤ) (hx: x ∈ U) : 0 ≤ x - lb := by
    apply Int.le_sub_left_of_add_le
    rw [Int.add_zero]; apply hlb
    assumption
  let X : Set ℕ := U.image fun z => (z - lb).toNat
  have Xnonempty: X.Nonempty := by
    apply Set.image_nonempty_iff.mpr
    assumption
  replace Xnonempty: ∃x, x ∈ X := by obtain ⟨x, hx⟩ := Xnonempty; exists x
  have ⟨i, hi, eq⟩ := Set.mem_image.mp (Nat.find_spec Xnonempty)
  rw [show ⨅ U = Nat.find Xnonempty + lb from ?_]
  rwa [←eq, Int.toNat_of_nonneg, Int.sub_add_cancel]
  apply hlb'; assumption
  apply le_antisymm
  · apply csInf_le
    exists lb
    rwa [←eq, Int.toNat_of_nonneg, Int.sub_add_cancel]
    apply hlb'; assumption
  · apply le_csInf
    assumption
    intro x hx
    rw [←not_lt]; intro h
    refine Nat.find_minimal Xnonempty (x - lb).toNat ?_ ?_
    apply Int.ofNat_lt.mp
    rwa [Int.toNat_of_nonneg, Int.sub_lt_iff]
    apply hlb'; assumption
    apply Set.mem_image'
    assumption
