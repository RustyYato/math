import LeanMath.Tactic.PPWithUniv
import LeanMath.Tactic.AxiomBlame
import LeanMath.Data.Equiv.Antisymm
import LeanMath.Data.Equiv.Basic
import LeanMath.Order.Defs
import LeanMath.Data.Fintype.Order

instance Type.instSetoid : Setoid (Type u) where
  r a b := Nonempty (a ≃ b)
  iseqv := {
    refl _ := ⟨.id _⟩
    symm := fun ⟨h⟩ => ⟨h.symm⟩
    trans := fun ⟨h⟩ ⟨g⟩ => ⟨h.trans g⟩
  }

@[pp_with_univ]
structure Cardinal.{u} where
  ofQuot :: toQuot : Quotient Type.instSetoid.{u}

namespace Cardinal

def type (α: Type u) : Cardinal.{u} where
  toQuot := Quotient.mk _ α

@[cases_eliminator]
def ind {motive: Cardinal -> Prop} (type: ∀α, motive (type α)) (c: Cardinal) : motive c := by
  cases c with | ofQuot c =>
  induction c using Quotient.ind with | _ c =>
  apply type

def lift (f: Type u -> A) (h: ∀α β: Type u, α ≈ β -> f α = f β) : Cardinal -> A
| .ofQuot c => c.lift f h
def lift₂ (f: Type u -> Type v -> A) (h: ∀α₀ β₀ α₁ β₁, (α₀ ≃ α₁) -> (β₀ ≃ β₁) -> f α₀ β₀ = f α₁ β₁) : Cardinal -> Cardinal -> A
| .ofQuot a, .ofQuot b => a.liftOn₂ b f (fun a b c d ⟨h₀⟩ ⟨h₁⟩ => h a b c d h₀ h₁)

@[simp] def lift_type (f: Type u -> A) (h: ∀α β: Type u, α ≈ β -> f α = f β) (α: Type u) : lift f h (type α) = f α := rfl
@[simp] def lift₂_type (f: Type u -> Type v -> A) (h) (α: Type u) (β: Type v) : lift₂ f h (type α) (type β) = f α β := rfl

def sound (h: α ≃ β) : type α = type β := by
  show ofQuot _ = ofQuot _
  congr 1
  apply Quotient.sound
  exact ⟨h⟩

def exact (h: type α = type β) : α ≈ β := Quotient.exact (Cardinal.ofQuot.inj h)
noncomputable def exact' (h: type α = type β) : α ≃ β := Classical.choice (Quotient.exact (Cardinal.ofQuot.inj h))

instance : LE Cardinal.{u} where
  le := lift₂ (fun α β => Nonempty (α ↪ β)) <| by
    intro α₀ β₀ α₁ β₁ f g
    dsimp
    simp; apply Iff.intro
    intro ⟨h⟩
    exact ⟨Equiv.embed_congr f g h⟩
    intro ⟨h⟩
    exact ⟨(Equiv.embed_congr f g).symm h⟩

instance : LT Cardinal.{u} where
  lt a b := a ≤ b ∧ ¬b ≤ a

instance : IsPartialOrder Cardinal.{u} where
  lt_iff_le_and_not_ge := Iff.rfl
  refl x := by
    cases x
    exact ⟨Embedding.id _⟩
  trans := by
    intro a b c h g
    cases a with | _ α =>
    cases b with | _ β =>
    cases c with | _ γ =>
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    exact ⟨h.trans g⟩
  antisymm := by
    intro a b
    cases a with | _ α =>
    cases b with | _ β =>
    intro ⟨f⟩ ⟨g⟩
    apply sound
    apply Equiv.antisymm
    assumption
    assumption

instance : Add Cardinal.{u} where
  add := lift₂ (type <|· ⊕ ·) <| by
    intro _ _ _ _ h g
    apply sound
    apply Equiv.sum_congr
    assumption
    assumption

instance : Mul Cardinal.{u} where
  mul := lift₂ (type <|· × ·) <| by
    intro _ _ _ _ h g
    apply sound
    apply Equiv.prod_congr
    assumption
    assumption

instance : Pow Cardinal.{u} Cardinal.{u} where
  pow := lift₂ (fun α β => type <| β -> α) <| by
    intro _ _ _ _ h g
    apply sound
    apply Equiv.fun_congr
    assumption
    assumption

def ofNat (n: ℕ) : Cardinal := type (Fin n)

def ulift.{v, u} : Cardinal.{u} -> Cardinal.{max u v} :=
  lift (fun x => type (ULift x)) <| by
    intro α β ⟨h⟩
    apply sound
    exact Equiv.ulift_congr h

instance : NatCast Cardinal.{u} where
  natCast n := ulift (ofNat n)

instance : Pow Cardinal ℕ where
  pow a n := a ^ (n: Cardinal)

instance : SMul ℕ Cardinal.{u} where
  smul n a := n * a

instance : OfNat Cardinal n := ⟨n⟩

def exists_eq_type (c: Cardinal.{u}) : ∃α: Type u, type α = c := by
  cases c
  exact ⟨_, rfl⟩
def out (c: Cardinal.{u}) : Type u := Classical.choose c.exists_eq_type
def out_spec (c: Cardinal.{u}) : type c.out = c := Classical.choose_spec c.exists_eq_type

def sum {ι: Type v} (f: ι -> Cardinal.{u}) : Cardinal.{max v u} := type (Σi, (f i).out)
def prod {ι: Type v} (f: ι -> Cardinal.{u}) : Cardinal.{max v u} := type (∀i, (f i).out)

def ω := ulift (type Nat)

def type_of_empty (α: Type*) [IsEmpty α] : type α = 0 := by
  apply sound
  apply Equiv.empty

private noncomputable def of_not_eq_fin_pre (α: Type*) (h: ∀x: ℕ, type α ≠ x)
  (limit: ℕ) : Fin limit ↪ α :=
  match limit with
  | 0 =>
    {
      toFun := nofun
      inj := nofun
    }
  | limit + 1 =>
    have f := of_not_eq_fin_pre α h limit
    let U : Set α := (Set.range f)ᶜ
    have : U.Nonempty := by
      simp [U]
      apply Classical.byContradiction
      intro hf; simp at hf
      have mem_range : (Set.range f)ᶜ = ⊤ᶜ := by rw [hf, Set.compl_top]; rfl
      replace mem_range := Set.scompl_inj.mp mem_range
      have : Fin limit ↭ α := {
        toFun := f
        inj' := f.inj
        surj' := by
          intro a
          have : a ∈ (⊤: Set α) := True.intro
          rw [←mem_range] at this
          simp at this
          obtain ⟨a, ha⟩ := this
          exact ⟨_, ha.symm⟩
      }
      replace this := Equiv.ofBij this
      refine h limit (sound ?_)
      apply this.symm.trans
      apply Equiv.ulift
    have exists_mem : ∃x, x ∈ U := by
      obtain ⟨x, hx⟩ := this
      exists x
    let top := Classical.choose exists_mem
    have top_mem : top ∉ Set.range f := Classical.choose_spec exists_mem
    {
      toFun i :=
        if hi:i < limit then
          f ⟨_, hi⟩
        else
          top
      inj := by
        intro i j
        simp at top_mem
        cases i using Fin.lastCases <;>
        cases j using Fin.lastCases <;> simp
        intro h; nomatch top_mem _ h
        intro h; nomatch top_mem _ h.symm
        intro h
        rw [f.inj h]
    }

private def of_not_eq_fin_pre_consistent'
  (α: Type*) (h: ∀x: ℕ, type α ≠ x)
  (g: ∃ x, x ∈ (Set.range ⇑(of_not_eq_fin_pre α h i))ᶜ)
  (hi: i < limit) :
  Classical.choose g = (of_not_eq_fin_pre α h limit) ⟨i, hi⟩ := by
  induction limit with
  | zero => nomatch hi
  | succ limit ih =>
    show _ = (if _:_ then _ else _)
    simp [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hi
    rcases hi with hi | rfl
    · rw [dif_pos hi]
      apply ih
    · rw [dif_neg]
      apply Nat.lt_irrefl

private def of_not_eq_fin_pre_consistent (α: Type*)
  (h: ∀x: ℕ, type α ≠ x) (limit₀ limit₁: ℕ) (i: ℕ) (h₀: i < limit₀) (h₁: i < limit₁) : of_not_eq_fin_pre α h limit₀ ⟨i, h₀⟩ = of_not_eq_fin_pre α h limit₁ ⟨i, h₁⟩ := by
  induction limit₀ generalizing limit₁ i with
  | zero => nomatch h₀
  | succ limit₀ ih =>
  cases limit₁ with
  | zero => nomatch h₁
  | succ limit₁ =>
    simp [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at h₀ h₁
    unfold of_not_eq_fin_pre
    dsimp; show (if _:_ then _ else _) = (if _:_ then _ else _)
    rcases h₀ with h₀ | rfl <;> rcases h₁ with h₁ | rfl
    · rw [dif_pos h₀, dif_pos h₁]
      apply ih
    · rw [dif_pos h₀, dif_neg]
      · symm; simp
        apply of_not_eq_fin_pre_consistent'
      · apply Nat.lt_irrefl
    · rw [dif_neg, dif_pos h₁]
      · simp
        apply of_not_eq_fin_pre_consistent'
      · apply Nat.lt_irrefl
    · rw [dif_neg]
      apply Nat.lt_irrefl

attribute [irreducible] of_not_eq_fin_pre

private noncomputable def of_not_eq_fin (α: Type*) (h: ∀x: ℕ, type α ≠ x) : ℕ ↪ α where
  toFun i := of_not_eq_fin_pre α h (i + 1) (Fin.last _)
  inj := by
    intro i j eq
    simp at eq
    let max := ((i + 1) ⊔ (j + 1))
    rw [of_not_eq_fin_pre_consistent α h (i + 1) max _ (by simp) (by
      simp only [max]
      apply lt_of_lt_of_le
      apply Fin.isLt
      apply left_le_max)] at eq
    rw [of_not_eq_fin_pre_consistent α h (j + 1) max _ (by simp) (by
      simp only [max]
      apply lt_of_lt_of_le
      apply Fin.isLt
      apply right_le_max)] at eq
    replace eq := Embedding.inj _ eq
    simpa using eq

def lt_omega_iff_natCast : ∀{x}, x < ω ↔ ∃n: ℕ, x = n := by
  intro x; apply Iff.intro
  · cases x with | _ α =>
    intro ⟨⟨f⟩, g⟩
    replace f := f.trans (Equiv.ulift ℕ).symm.toEmbedding
    replace g : ∀f: ℕ -> α, ¬Function.Injective f := by
      intro f hf; apply g ⟨?_⟩
      apply (Equiv.ulift ℕ).symm.toEmbedding.trans
      exact ⟨f, hf⟩
    apply Classical.byContradiction
    intro h; simp at h
    have := of_not_eq_fin α h
    exact g this this.inj
  · rintro ⟨n, rfl⟩
    have le : n ≤ ω := ?_
    refine ⟨?_, ?_⟩
    assumption
    intro f
    replace ⟨f⟩ := exact (le_antisymm f le)
    replace f := (Equiv.equiv_congr (Equiv.ulift _) (Equiv.ulift _)).symm f
    clear le
    let max : ℕ := max_of_range f.symm
    have : _ ≤ max := le_max_of_range (f (max + 1)) f.symm
    simp at this
    exact Nat.not_lt_of_le this (Nat.lt_succ_self _)
    refine ⟨?_⟩
    apply Equiv.embed_congr (Equiv.ulift _) (Equiv.ulift _) _
    exact Embedding.fin_val

def fintype_card (α: Type*) [Fintype α] : type α = Fintype.card α := by
  classical
  induction Fintype.finEquiv α with | _ =>
  apply sound
  apply Equiv.trans _ (Equiv.ulift _)
  apply Equiv.symm
  assumption

def lt_two_pow (a: Cardinal) : a < 2 ^ a := by
  cases a with | _ α =>
  apply And.intro
  refine ⟨?_⟩
  apply Equiv.embed_congr (Equiv.id _) (
    Equiv.fun_congr (Equiv.id _) (Equiv.bool_eqv_fin2.trans (Equiv.ulift _))
  ) _
  classical
  refine {
    toFun a b := a = b
    inj := ?_
  }
  intro a b h
  simpa using congrFun h b
  intro ⟨f⟩
  replace f := Equiv.embed_congr (
    Equiv.fun_congr (Equiv.id _) (Equiv.bool_eqv_fin2.trans (Equiv.ulift _)).symm
  ) (Equiv.id _) f
  exact Embedding.cantor f

end Cardinal
