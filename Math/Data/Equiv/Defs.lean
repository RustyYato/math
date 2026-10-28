module

public import Math.Data.Hom.Defs
import Math.Tactic.Basic

public structure Equiv (α β: Sort*) extends Hom α β where
  invFun: β -> α
  leftInv: Function.LeftInverse toFun invFun
  rightInv: Function.RightInverse toFun invFun

infixr:50 " ≃ " => Equiv

public class EquivLike (F: Sort*) (α β: outParam Sort*) extends Funlike F α β where
  coeInv (f: F) : β -> α := by intro f; exact f.invFun
  leftInv (f: F): Function.LeftInverse (coeFun f) (coeInv f) := by intro f; exact f.leftInv
  rightInv (f: F): Function.RightInverse (coeFun f) (coeInv f) := by intro f; exact f.rightInv

@[coe, expose] public def Equiv.coe [EquivLike F α β] (f: F) : α ≃ β where
  toFun := f
  invFun := EquivLike.coeInv f
  leftInv := EquivLike.leftInv f
  rightInv := EquivLike.rightInv f

public instance [EquivLike F α β] : CoeOut F (α ≃ β) where
  coe := Equiv.coe
namespace Equiv

public instance : EquivLike (α ≃ β) α β where
  coeInj := by
    intro a b h
    dsimp at h
    suffices a.invFun = b.invFun by
      obtain ⟨⟨a⟩, _, _, _⟩ := a
      obtain ⟨⟨b⟩, _, _, _⟩ := b
      congr
    ext i
    apply a.rightInv.injective
    rw [a.leftInv, h, b.leftInv]

@[expose] public protected def id (α: Sort*) : α ≃ α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl

variable {α β γ: Sort*}

@[expose] public protected def symm (f: α ≃ β) : β ≃ α where
  toFun := f.invFun
  invFun := f.toFun
  leftInv := f.rightInv
  rightInv := f.leftInv

@[ext] public theorem ext (f g: α ≃ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

@[simp] public theorem apply_id : Equiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃ β) : f.symm.symm = f := rfl

@[expose] public protected def comp (f: β ≃ γ) (g: α ≃ β) : α ≃ γ where
  toFun := f ∘ g
  invFun := g.symm ∘ f.symm
  leftInv x := by dsimp; rw [g.symm_apply, f.symm_apply]
  rightInv x := by dsimp; rw [f.apply_symm, g.apply_symm]
@[expose] public protected def trans (f: α ≃ β) (g: β ≃ γ) : α ≃ γ := g.comp f

@[simp] public theorem apply_comp (f: β ≃ γ) (g: α ≃ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃ β) (g: β ≃ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃ β) : f.symm.comp f = Equiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃ β) : f.comp f.symm = Equiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃ β) : f.symm.trans f = Equiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃ β) : f.trans f.symm = Equiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃ β) : Function.Surjective f := f.symm.rightInv.surjective

@[simp] public theorem normalize_toFun (f: α ≃ β) : f.toFun = f := rfl
