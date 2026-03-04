import LeanMath.Data.Equiv.Defs
import LeanMath.Data.Bijection.Basic

namespace Equiv

def prod_equiv_pprod : α × β ≃ α ×' β where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

def sum_equiv_psum : α ⊕ β ≃ α ⊕' β where
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

def optionCongr (f: α ≃ β) : Option α ≃ Option β where
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

@[simp] def apply_optionCongr_none (f: α ≃ β) : optionCongr f .none = .none := rfl
@[simp] def symm_apply_optionCongr_none (f: α ≃ β) : (optionCongr f).symm .none = .none := rfl
@[simp] def apply_optionCongr_some (f: α ≃ β) (a: α) : optionCongr f (.some a) = .some (f a) := rfl
@[simp] def symm_apply_optionCongr_some (f: α ≃ β) (b: β) : (optionCongr f).symm (.some b) = .some (f.symm b) := rfl

def psumCongr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : α₀ ⊕' β₀ ≃ α₁ ⊕' β₁ where
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

def liftSum : (α₀ ⊕' β₀ ≃ α₁ ⊕' β₁) ≃ (α₀ ⊕ β₀ ≃ α₁ ⊕ β₁) where
  toFun f := sum_equiv_psum.trans <| f.trans sum_equiv_psum.symm
  invFun f := sum_equiv_psum.symm.trans <| f.trans sum_equiv_psum
  leftInv f := by
    apply DFunLike.ext; intro x
    simp
  rightInv f := by
    apply DFunLike.ext; intro x
    simp

def sumCongr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : α₀ ⊕ β₀ ≃ α₁ ⊕ β₁ := liftSum (psumCongr f g)

@[simp] def apply_psumCongr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : psumCongr f g (.inl x) = .inl (f x) := rfl
@[simp] def apply_psumCongr_inr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : psumCongr f g (.inr x) = .inr (g x) := rfl
@[simp] def symm_apply_psumCongr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (psumCongr f g).symm (.inl x) = .inl (f.symm x) := rfl
@[simp] def symm_apply_psumCongr_inr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (psumCongr f g).symm (.inr x) = .inr (g.symm x) := rfl

@[simp] def apply_sumCongr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : sumCongr f g (.inl x) = .inl (f x) := rfl
@[simp] def apply_sumCongr_inr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : sumCongr f g (.inr x) = .inr (g x) := rfl
@[simp] def symm_apply_sumCongr_inl (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (sumCongr f g).symm (.inl x) = .inl (f.symm x) := rfl
@[simp] def symm_apply_sumCongr_inr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : (sumCongr f g).symm (.inr x) = .inr (g.symm x) := rfl

end Equiv
