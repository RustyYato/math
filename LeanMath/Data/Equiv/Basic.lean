import LeanMath.Data.Equiv.Defs
import LeanMath.Data.Bijection.Basic
import LeanMath.Tactic.AxiomBlame

namespace Equiv

def equiv_congr (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ≃ β₀) ≃ (α₁ ≃ β₁) where
  toFun f := h.symm.trans (f.trans g)
  invFun f := h.trans (f.trans g.symm)
  leftInv f := by
    simp; rw [←Equiv.trans_assoc]
    simp
  rightInv f := by
    simp; rw [←Equiv.trans_assoc]
    simp

def prod_equiv_pprod : (α × β) ≃ (α ×' β) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

def sum_equiv_psum : (α ⊕ β) ≃ (α ⊕' β) where
  toFun
  | .inl x => .inl x
  | .inr x => .inr x
  invFun
  | .inl x => .inl x
  | .inr x => .inr x
  leftInv
  | .inl _ => rfl
  | .inr _ => rfl
  rightInv
  | .inl _ => rfl
  | .inr _ => rfl

def option_congr (f: α ≃ β) : Option α ≃ Option β where
  toFun
  | .some a => .some (f a)
  | .none => .none
  invFun
  | .some a => .some (f.symm a)
  | .none => .none
  leftInv := by
    intro a; cases a
    rfl
    show some _ = some _
    rw [f.symm_coe]
  rightInv := by
    intro a; cases a
    rfl
    show some _ = some _
    rw [f.coe_symm]

@[simp] def apply_option_congr_none (f: α ≃ β) : option_congr f .none = .none := rfl
@[simp] def symm_apply_option_congr_none (f: α ≃ β) : (option_congr f).symm .none = .none := rfl
@[simp] def apply_option_congr_some (f: α ≃ β) (a: α) : option_congr f (.some a) = .some (f a) := rfl
@[simp] def symm_apply_option_congr_some (f: α ≃ β) (b: β) : (option_congr f).symm (.some b) = .some (f.symm b) := rfl

def psum_congr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ⊕' β₀) ≃ (α₁ ⊕' β₁) where
  toFun
  | .inl x => .inl (f x)
  | .inr x => .inr (g x)
  invFun
  | .inl x => .inl (f.symm x)
  | .inr x => .inr (g.symm x)
  leftInv x := by
    cases x
    show PSum.inl _ = PSum.inl _
    rw [f.symm_coe]
    show PSum.inr _ = PSum.inr _
    rw [g.symm_coe]
  rightInv x := by
    cases x
    show PSum.inl _ = PSum.inl _
    rw [f.coe_symm]
    show PSum.inr _ = PSum.inr _
    rw [g.coe_symm]

def pprod_congr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ×' β₀) ≃ (α₁ ×' β₁) where
  toFun x := ⟨f x.1, g x.2⟩
  invFun x := ⟨f.symm x.1, g.symm x.2⟩
  leftInv x := by simp
  rightInv x := by simp

def liftSum : ((α₀ ⊕' β₀) ≃ (α₁ ⊕' β₁)) ≃ ((α₀ ⊕ β₀) ≃ (α₁ ⊕ β₁)) :=
  (equiv_congr sum_equiv_psum sum_equiv_psum).symm

def liftProd : ((α₀ ×' β₀) ≃ (α₁ ×' β₁)) ≃ ((α₀ × β₀) ≃ (α₁ × β₁)) :=
  (equiv_congr prod_equiv_pprod prod_equiv_pprod).symm

def sum_congr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ⊕ β₀) ≃ (α₁ ⊕ β₁) := liftSum (psum_congr f g)

def prod_congr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ×  β₀) ≃ (α₁ × β₁) := liftProd (pprod_congr f g)

@[simp] def apply_psum_congr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : psum_congr f g (.inl x) = .inl (f x) := rfl
@[simp] def apply_psum_congr_inr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : psum_congr f g (.inr x) = .inr (g x) := rfl
@[simp] def symm_psum_congr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (psum_congr f g).symm = psum_congr f.symm g.symm := rfl

@[simp] def apply_sum_congr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : sum_congr f g (.inl x) = .inl (f x) := rfl
@[simp] def apply_sum_congr_inr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : sum_congr f g (.inr x) = .inr (g x) := rfl
@[simp] def symm_sum_congr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (sum_congr f g).symm = sum_congr f.symm g.symm := rfl

@[simp] def apply_pprod_congr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : pprod_congr f g x = ⟨f x.1, g x.2⟩ := rfl
@[simp] def symm_pprod_congr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (pprod_congr f g).symm = pprod_congr f.symm g.symm := rfl

@[simp] def apply_prod_congr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : prod_congr f g x = ⟨f x.1, g x.2⟩ := rfl
@[simp] def symm_prod_congr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (prod_congr f g).symm = prod_congr f.symm g.symm := rfl

def subtype_congr {P: α -> Prop} {Q: β -> Prop} (f: α ≃ β) (h: ∀x, P x ↔ Q (f x)) : Subtype P ≃ Subtype Q where
  toFun x := {
    val := f x.val
    property := (h x.val).mp x.property
  }
  invFun x := {
    val := f.symm x.val
    property := by
      apply (h _).mpr
      simp; exact x.property
  }
  leftInv x := by simp
  rightInv x := by simp

def emb_eq_subtype : (α ↪ β) ≃ { f: α -> β // Function.Injective f } where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

def fun_congr (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ -> β₀) ≃ (α₁ -> β₁) where
  toFun f := g ∘ f ∘ h.symm
  invFun f := g.symm ∘ f ∘ h
  leftInv f := by
    show (g.symm.trans g) ∘ f ∘ (h.symm.trans h) = _
    simp; rfl
  rightInv f := by
    show (g.trans g.symm) ∘ f ∘ (h.trans h.symm) = _
    simp; rfl

@[simp] def symm_fun_congr (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (fun_congr h g).symm = fun_congr h.symm g.symm := rfl
@[simp] def apply_fun_congr (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) (f: α₀ -> β₀) : fun_congr h g f = g ∘ f ∘ h.symm := rfl

def embed_congr (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (α₀ ↪ β₀) ≃ (α₁ ↪ β₁) :=
  equiv_congr emb_eq_subtype.symm emb_eq_subtype.symm <|
  subtype_congr (fun_congr h g) <| by
  intro f
  apply Iff.intro
  · intro hf x y
    simp
    intro eq
    apply h.symm.inj
    exact hf (inj g eq)
  · intro hf x y eq
    have := @hf (h x) (h y)
    simp at this
    rw [eq] at this
    exact inj h (this rfl)

@[simp] def symm_embed_congr (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (embed_congr h g).symm = embed_congr h.symm g.symm := rfl
@[simp] def apply_embed_congr (h: α₀ ≃ α₁) (g: β₀ ≃ β₁) (f: α₀ ↪ β₀) : embed_congr h g f = (g.toEmbedding.comp f).comp h.symm.toEmbedding := rfl

section

variable {α₀ α₁: Sort*} {β₀: α₀ -> Sort*} {β₁: α₁ -> Sort*}
variable (f: α₀ ≃ α₁)

private def symm_cast_eq (g: ∀a, β₀ a ≃ β₁ (f a)) (h: a = b) : (g a).symm (cast (by simp [h]) ((g b) hx)) ≍ hx := by
  subst h
  simp

def psigma_congr (g: ∀a, β₀ a ≃ β₁ (f a)) : (Σ'a, β₀ a) ≃ (Σ'a, β₁ a) where
 toFun x := ⟨f x.1, g _ x.2⟩
 invFun x := ⟨f.symm x.1, (g _).symm (cast (by simp) x.2)⟩
 leftInv := by
  intro ⟨x, hx⟩
  simp
 rightInv := by
  intro ⟨x, hx⟩
  dsimp
  have : f.symm (f x) = x := by simp
  congr
  apply symm_cast_eq
  simp

def dfun_congr (g: ∀a, β₀ (f.symm a) ≃ β₁ a) : (∀a, β₀ a) ≃ (∀a, β₁ a) where
 toFun F x := g _ (F (f.symm x))
 invFun F x := cast (by simp) <| (g _).symm (F (f x))
 leftInv F := by
  ext x; simp
  apply inj (g x).symm
  simp
  apply eq_of_heq
  apply (cast_heq _ _).trans
  congr <;> simp
  apply Function.hfunext
  simp
  intro a₀ a₁ h
  rfl
 rightInv F := by
  ext x; simp
  apply eq_of_heq
  apply (cast_heq _ _).trans
  congr; simp

end

section

variable {α₀ α₁: Type*} {β₀: α₀ -> Type*} {β₁: α₁ -> Type*}
variable (f: α₀ ≃ α₁) (g: ∀a, β₀ a ≃ β₁ (f a))

def sigma_equiv_psigma {α: Type*} {β: α -> Type*} : (Σa, β a) ≃ (Σ'a, β a) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

def lift_sigma : ((Σ'a, β₀ a) ≃ (Σ'a, β₁ a)) ≃ ((Σa, β₀ a) ≃ (Σa, β₁ a)) :=
  (equiv_congr sigma_equiv_psigma sigma_equiv_psigma).symm

def sigma_congr : (Σa, β₀ a) ≃ (Σa, β₁ a) := lift_sigma (psigma_congr f g)

def fin_eqv_suptype (n: ℕ) : Fin n ≃ { x // x < n } where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

def swap [DecidableEq α] (a b: α) (f: α ≃ β) : α ≃ β where
  toFun x := if x = a then f b else if x = b then f a else f x
  invFun x := if f.symm x = a then b else if f.symm x = b then a else f.symm x
  leftInv := by
    intro b'
    simp
    split <;> rename_i h₀; subst a
    simp; intro g; subst g; simp
    split; rw [if_pos rfl]
    subst b; simp
    rw [if_neg]; simp
    rename_i h₁
    intro g
    have := g h₀
    contradiction
  rightInv := by
    intro a'
    simp
    split <;> rename_i h₀; subst a; simp
    split; subst a'; simp
    simp [if_neg h₀]; intro; contradiction

def apply_swap [DecidableEq α] (a b x: α) (f: α ≃ β) :
  f.swap a b x = if x = a then f b else if x = b then f a else f x := rfl

def symm_swap [DecidableEq α] [DecidableEq β] (a b: α) (f: α ≃ β) :
  (f.swap a b).symm = f.symm.swap (f a) (f b) := by
  apply DFunLike.ext; intro x
  show (if f.symm x = a then b else if f.symm x = b then a else f.symm x) = _
  rw [apply_swap]
  simp
  split; subst a
  simp
  split; subst b; simp
  intro h; rw [h]; simp
  rw [if_neg, if_neg]
  rintro rfl; simp at *
  rintro rfl; simp at *

def set [DecidableEq α] (a: α) (b: β) (f: α ≃ β) : α ≃ β :=
  f.swap a (f.symm b)

def symm_set [DecidableEq α] [DecidableEq β]
  (a: α) (b: β) (f: α ≃ β) : (f.set a b).symm = f.symm.set b a := by
  simp [set]
  apply DFunLike.ext; intro x
  rw [symm_swap, apply_swap, apply_swap]
  simp
  split; subst x
  simp; intro h; rw [←h]; simp
  split; rfl
  rfl

def of_fin_succ (f: Fin (n + 1) ≃ Fin (m + 1)) : Fin n ≃ Fin m :=
  let f := f.set (Fin.last _) (Fin.last _)
  {
    toFun x := ⟨f x.castSucc, by
      have := (f x.castSucc).isLt; rw [Nat.lt_succ_iff] at this
      rcases Nat.lt_or_eq_of_le this with h | h
      assumption
      replace h : _ = (Fin.last _).val := h
      have : f.symm (Fin.last _) = x.val := by
        rw [←Fin.val_inj.mp h]
        simp
      simp [f, symm_set] at this
      simp [set, apply_swap] at this
      have : x.val < x.val := this ▸ x.isLt
      have := Nat.lt_irrefl _ this
      contradiction⟩
    invFun x := ⟨f.symm x.castSucc, by
      have := (f.symm x.castSucc).isLt; rw [Nat.lt_succ_iff] at this
      rcases Nat.lt_or_eq_of_le this with h | h
      assumption
      replace h : _ = (Fin.last _).val := h
      have : f (Fin.last _) = x.val := by
        rw [←Fin.val_inj.mp h]
        simp
      simp [f] at this
      simp [set, apply_swap] at this
      have : x.val < x.val := this ▸ x.isLt
      have := Nat.lt_irrefl _ this
      contradiction⟩
    leftInv := by intro x; simp
    rightInv := by intro x; simp
  }

def of_fin_eqv (h: Fin n ≃ Fin m) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m => exact (h.symm 0).elim0
  | succ n ih =>
    cases m with
    | zero => exact (h 0).elim0
    | succ m => rw [ih (of_fin_succ h)]

end

end Equiv
