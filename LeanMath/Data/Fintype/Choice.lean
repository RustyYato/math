import LeanMath.Data.Fintype.Defs

variable {ι: Sort*}

private def finTruncChoice' {α: Fin n -> Sort*} (h: ∀i, Trunc (α i)) : Trunc (∀i, α i) :=
  match n with
  | 0 => .mk nofun
  | _ + 1 =>
    (finTruncChoice' (h := fun i => h i.succ)).bind fun f₁ =>
    (h 0).map fun f₀ => fun
      | ⟨0, _⟩ => f₀
      | ⟨i + 1, hi⟩ => f₁ ⟨i, Nat.lt_of_succ_lt_succ hi⟩

def finTruncChoice [DecidableEq ι] [ft: Fintype ι] {α: ι -> Sort*} (h: ∀i, Trunc (α i)) : Trunc (∀i, α i) :=
  (Fintype.finEquiv ι).bind fun eqv: _ ≃ _ =>
  (finTruncChoice' (n := Fintype.card ι) (α := α ∘ eqv) (h := fun i => h _)).map fun f i =>
  cast (by simp) (f (eqv.symm i))

private def finChoose' {α: Fin n -> Sort*} (h: ∀i, Nonempty (α i)) : Nonempty (∀i, α i) := by
  induction n with
  | zero => exact ⟨nofun⟩
  | succ n ih =>
    have ⟨f₀⟩ := h 0
    have ⟨f₁⟩ := ih (fun i => h _) (α := α ∘ Fin.succ)
    refine ⟨fun
      | ⟨0, _⟩ => f₀
      | ⟨i + 1, hi⟩ => f₁ ⟨i, Nat.lt_of_succ_lt_succ hi⟩⟩

def finChoose [DecidableEq ι] [ft: Finite ι] {α: ι -> Sort*} (h: ∀i, Nonempty (α i)) : Nonempty (∀i, α i) := by
  have ⟨ft⟩ := ft
  induction (Fintype.finEquiv ι) with | mk eqv =>
  suffices Nonempty (∀i: Fin (Fintype.card ι), α (eqv i)) by
    obtain ⟨f⟩ := this
    refine ⟨fun i => ?_⟩
    rw [←Equiv.symm_coe eqv i]
    apply f
  apply finChoose'
  intro i; apply h

def finChoice [DecidableEq ι] [ft: Finite ι] {α: ι -> Sort*} {P: ∀{i}, α i -> Prop} (h: ∀i, ∃a: α i, P a) : ∃f: ∀i, α i, ∀i, P (f i) := by
  have ⟨f⟩ := finChoose (ι := ι) (α := fun i: ι => { a: α i // P a }) ?_
  exists fun i => (f i).val
  intro i
  apply Subtype.property
  intro i
  have ⟨a, pa⟩ := h i
  exact ⟨a, pa⟩
