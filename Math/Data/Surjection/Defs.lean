module

public import Math.Data.Hom.Defs
import Math.Tactic.Basic

public structure Surjection (α β: Sort*) extends Hom α β where
  protected surjective: Function.Surjective toFun

infixr:50 " ↠ " => Surjection

public class SurjectionLike (F: Sort*) (α β: outParam Sort*) extends Funlike F α β where
  coeSurjection (f: F): Function.Surjective f := by intro f; first|exact f.surjective|exact f.surj

@[coe, expose] public def Surjection.coe [SurjectionLike F α β] (f: F) : α ↠ β where
  toFun := f
  surjective := SurjectionLike.coeSurjection f

public instance [SurjectionLike F α β] : CoeOut F (α ↠ β) where
  coe := Surjection.coe
namespace Surjection

public instance : SurjectionLike (α ↠ β) α β where

@[expose] public protected def id (α: Sort*) : α ↠ α where
  toFun := id
  surjective _ := ⟨_, rfl⟩

variable {α β γ: Sort*}

@[ext] public theorem ext (f g: α ↠ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

public theorem surj (f: α ↠ β) : Function.Surjective f := f.surjective

@[simp] public theorem apply_id : Surjection.id α x = x := rfl

@[expose] public protected def comp (f: β ↠ γ) (g: α ↠ β) : α ↠ γ where
  toFun := f ∘ g
  surjective := f.surj.comp g.surj
@[expose] public protected def trans (f: α ↠ β) (g: β ↠ γ) : α ↠ γ := .comp g f

@[simp] public theorem apply_comp (f: β ↠ γ) (g: α ↠ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↠ β) (g: β ↠ γ) (x: α) : f.trans g x = g (f x) := rfl

@[simp] public theorem normalize_toFun (f: α ↠ β) : f.toFun = f := rfl
