import LeanMath.Logic.Funlike
import LeanMath.Data.Bijection.Defs

structure Equiv (α β: Sort*) where
  toFun: α -> β
  invFun: β -> α
  leftInv: Function.LeftInverse toFun invFun
  rightInv: Function.RightInverse toFun invFun

infixr:20 " ≃ " => Equiv

namespace Equiv

instance : FunLike (α ≃ β) α β where
  coeInj := by
    intro a b h
    dsimp at h
    suffices a.invFun = b.invFun by
      cases a; cases b
      congr
    ext x
    rw [←a.leftInv x, a.rightInv, h, b.rightInv]

protected def id (α: Sort*) : α ≃ α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl

def symm (f: α ≃ β) : β ≃ α where
  toFun := f.invFun
  invFun := f.toFun
  leftInv := f.rightInv
  rightInv := f.leftInv

def symm_coe (f: α ≃ β) (x: β) : f (f.symm x) = x := f.leftInv _
def coe_symm (f: α ≃ β) (x: α) : f.symm (f x) = x := f.rightInv _

def comp (f: β ≃ γ) (g: α ≃ β) : α ≃ γ where
  toFun := f ∘ g
  invFun := g.symm ∘ f.symm
  leftInv x := by
    dsimp
    rw [g.symm_coe, f.symm_coe]
  rightInv x := by
    dsimp
    rw [f.coe_symm, g.coe_symm]

abbrev trans (f: α ≃ β) (g: β ≃ γ) : α ≃ γ := g.comp f

@[simp] def apply_id (α: Sort*) (x: α) : Equiv.id α x = x := rfl
@[simp] def apply_comp (f: β ≃ γ) (g: α ≃ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_trans (f: β ≃ γ) (g: α ≃ β) (x: α) : (g.trans f) x = f (g x) := rfl

def toBij (f: α ≃ β) : α ↭ β where
  toFun := f
  inj' := f.rightInv.injective
  surj' := Function.RightInverse.surjective f.leftInv

end Equiv
