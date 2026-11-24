module

public import Math.Data.Equiv.Ext
public import Math.Logic.IsEmpty
import Math.Tactic.Basic

section

namespace Math.Equiv

public def empty (α β: Type*) [IsEmpty α] [IsEmpty β] : α ≃ β where
  toFun := elim_empty
  invFun := elim_empty
  leftInv := rec_elim_empty
  rightInv := rec_elim_empty

public def unique (α β: Type*) [Subsingleton α] [Subsingleton β] [Inhabited α] [Inhabited β] : α ≃ β where
  toFun := default
  invFun := default
  leftInv _ := Subsingleton.allEq _ _
  rightInv _ := Subsingleton.allEq _ _

@[expose] public def congr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ≃ β₀) ≃ (α₁ ≃ β₁) where
  toFun x := f.symm.trans (x.trans g)
  invFun x := f.trans (x.trans g.symm)
  leftInv x := by ext i; simp
  rightInv x := by ext i; simp

@[expose] public def ulift : ULift α ≃ α where
  toFun := ULift.down
  invFun := ULift.up
  leftInv _ := rfl
  rightInv _ := rfl
@[expose] public def plift : PLift α ≃ α where
  toFun := PLift.down
  invFun := PLift.up
  leftInv _ := rfl
  rightInv _ := rfl

@[expose] public def congr_ulift : (α ≃ β) ≃ (ULift α ≃ ULift β) :=
  (congr ulift ulift).symm

@[expose] public def congr_plift : (α ≃ β) ≃ (PLift α ≃ PLift β) :=
  (congr plift plift).symm

def erase_none' (f: Option α ≃ Option β) (a: α) : β :=
    if ha:f a = .none then
      (f .none).get <| by
        rw [Option.isSome_iff_ne_none]
        intro g; rw [←g] at ha
        nomatch f.inj ha
    else
      (f a).get <| by rwa [Option.isSome_iff_ne_none]

public def erase_none (f: Option α ≃ Option β) : α ≃ β where
  toFun := erase_none' f
  invFun := erase_none' f.symm
  leftInv a := by
    unfold erase_none'
    split
    · simp
      apply Option.some.inj; simp
      rename_i h; simp [←h]
    · rw [dite_eq_right] <;> simp
  rightInv b := by
    unfold erase_none'
    split
    · simp
      apply Option.some.inj; simp
      rename_i h; simp [←h]
    · rw [dite_eq_right] <;> simp

public def congr_option (f: α ≃ β) : (Option α ≃ Option β) where
  toFun x := x.map f
  invFun x := x.map f.symm
  leftInv x := by
    cases x <;> dsimp
    rw [f.symm_apply]
  rightInv x := by
    cases x <;> dsimp
    rw [f.apply_symm]

@[expose] public def congr_sum (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ⊕ β₀) ≃ (α₁ ⊕ β₁) where
  toFun x := x.map f g
  invFun x := x.map f.symm g.symm
  leftInv x := by cases x <;> simp
  rightInv x := by cases x <;> simp

@[expose] public def congr_prod (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ × β₀) ≃ (α₁ × β₁) where
  toFun x := x.map f g
  invFun x := x.map f.symm g.symm
  leftInv x := by cases x <;> simp
  rightInv x := by cases x <;> simp

@[expose] public def fin_cast (h: n = m) : Fin n ≃ Fin m where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  leftInv _ := rfl
  rightInv _ := rfl

@[expose] public def fin_castSucc : Fin (n + 1) ≃ Option (Fin n) where
  toFun x := if h:x.val < n then .some ⟨x, h⟩ else .none
  invFun
  | .none => ⟨n, Nat.lt_succ_self _⟩
  | .some x => x.castSucc
  leftInv x := by cases x <;> simp
  rightInv x := by
    cases x using Fin.lastCases <;> simp
    rfl

@[expose] public def fin_succ : Fin (n + 1) ≃ Option (Fin n) where
  toFun
  | ⟨0, _⟩ => .none
  | ⟨i + 1, h⟩ => .some ⟨i, Nat.lt_of_succ_lt_succ h⟩
  invFun
  | .none => ⟨0, Nat.zero_lt_succ _⟩
  | .some x => x.succ
  leftInv x := by cases x <;> simp [Fin.succ]
  rightInv x := by
    cases n <;>
    cases x using Fin.cases <;> simp [Fin.succ]
    rfl

@[expose] public def congr_pi {β₀: α₀ -> Sort*} {β₁: α₁ -> Sort*}
  (f: α₀ ≃ α₁) (g: ∀a, β₀ a ≃ β₁ (f a)) : (∀a, β₀ a) ≃ (∀a, β₁ a) where
  toFun x a := cast (by simp) (g _ (x (f.symm a)))
  invFun x a := (g _).symm (x (f a))
  leftInv x := by
    ext i; simp
    apply eq_of_heq; apply HEq.trans (cast_heq _ _)
    congr; simp
  rightInv x := by
    ext i; simp
    apply (g i).inj
    simp
    apply eq_of_heq; apply HEq.trans (cast_heq _ _)
    generalize hj:f.symm (f i) = j
    simp at hj; subst j; rfl

@[expose] public def congr_func (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ -> β₀) ≃ (α₁ -> β₁) :=
  congr_pi f (fun _ => g)

@[expose] public def congr_subtype {P: α -> Prop} {Q: β -> Prop}
  (f: α ≃ β) (hf: ∀a, P a ↔ Q (f a))
 : Subtype P ≃ Subtype Q where
  toFun x := {
    val := f x.val
    property := (hf _).mp x.property
  }
  invFun x := {
    val := f.symm x.val
    property := by
      apply (hf _).mpr
      simp
      exact x.property
  }
  leftInv x := by ext; simp
  rightInv x := by ext; simp

@[expose] public def embedding_eqv_subtype : (α ↪ β) ≃ { f: α -> β // Function.Injective f } where
  toFun f := {
    val := f
    property := f.inj
  }
  invFun f := {
    toFun := f
    injective := f.property
  }
  leftInv _ := rfl
  rightInv _ := rfl

@[expose] public def congr_embedding (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ↪ β₀) ≃ (α₁ ↪ β₁) :=
  (congr embedding_eqv_subtype embedding_eqv_subtype).symm <|
  congr_subtype (congr_func f g) <| by
  intro x
  apply Iff.intro
  intro hx a b h
  apply f.symm.inj
  apply hx
  exact g.inj h
  intro hx a b h
  apply f.inj
  apply hx
  show g _ = g _
  simp [h]

@[expose] public def surjection_eqv_subtype : (α ↠ β) ≃ { f: α -> β // Function.Surjective f } where
  toFun f := {
    val := f
    property := f.surj
  }
  invFun f := {
    toFun := f
    surjective := f.property
  }
  leftInv _ := rfl
  rightInv _ := rfl

@[expose] public def congr_surjection (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ↠ β₀) ≃ (α₁ ↠ β₁) :=
  (congr surjection_eqv_subtype surjection_eqv_subtype).symm <|
  congr_subtype (congr_func f g) <| by
  intro x
  apply Iff.intro
  intro hx b
  have ⟨a, ha⟩ := hx (g.symm b)
  exists f a
  change g _ = _
  simp [ha]
  intro hx b
  have ⟨a, ha⟩ := hx (g b)
  exists f.symm a
  apply g.inj
  rw [←ha]; rfl

@[expose] public def prod_sum : (γ × (α ⊕ β)) ≃ ((γ × α) ⊕ γ × β) where
  toFun
  | ⟨i, .inl a⟩ => .inl ⟨i, a⟩
  | ⟨i, .inr a⟩ => .inr ⟨i, a⟩
  invFun
  | .inl ⟨i, a⟩ => ⟨i, .inl a⟩
  | .inr ⟨i, a⟩ => ⟨i, .inr a⟩
  leftInv a := by cases a <;> rfl
  rightInv | ⟨i, a⟩ => by cases a <;> rfl

@[expose] public def prod_comm : (α × β) ≃ (β × α) where
  toFun := Prod.swap
  invFun := Prod.swap
  leftInv _ := rfl
  rightInv _ := rfl

@[expose] public def sum_comm : (α ⊕ β) ≃ (β ⊕ α) where
  toFun := Sum.swap
  invFun := Sum.swap
  leftInv a := by cases a <;> rfl
  rightInv a := by cases a <;> rfl

@[expose] public def prod_assoc : ((α × β) × γ) ≃ (α × (β × γ)) where
  toFun x := (x.1.1, x.1.2, x.2)
  invFun x := ((x.1, x.2.1), x.2.2)
  leftInv _ := rfl
  rightInv _ := rfl

@[expose] public def sum_assoc : ((α ⊕ β) ⊕ γ) ≃ (α ⊕ (β ⊕ γ)) where
  toFun
  | .inl (.inl x) => .inl x
  | .inl (.inr x) => .inr (.inl x)
  | .inr x => .inr (.inr x)
  invFun
  | .inl x => .inl (.inl x)
  | .inr (.inl x) => .inl (.inr x)
  | .inr (.inr x) => .inr x
  leftInv
  | .inl _
  | .inr (.inl _)
  | .inr (.inr _) => rfl
  rightInv
  | .inl (.inl _)
  | .inl (.inr _)
  | .inr _ => rfl

@[expose] public def option_func : (Option α -> β) ≃ ((α -> β) × β) where
  toFun f := (f ∘ Option.some, f .none)
  invFun
  | f, .some a => f.1 a
  | f, .none => f.2
  leftInv _ := rfl
  rightInv f := by ext i; cases i <;> rfl
