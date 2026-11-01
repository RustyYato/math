module

import Math.Tactic.TypeStar

public class DFunlike (F: Sort*) (α: outParam Sort*) (β: outParam (α -> Sort*)) where
  public coeFun (f: F) (a: α) : β a := by intro f; exact f.toFun
  public coeInj: Function.Injective coeFun := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply DFunlike.coeInj
      assumption

public abbrev Funlike (F: Sort*) (α β: Sort*) := DFunlike F α (fun _ => β)
public abbrev RelLike (F: Sort*) (α: Sort*) := Funlike F α (α -> Prop)

public instance [DFunlike F α β] : CoeFun F (fun _ => ∀x, β x) where
  coe := DFunlike.coeFun

public instance {α: Sort*} {β: α -> Sort*} : DFunlike (∀x: α, β x) α β where
  coeFun := id
  coeInj _ _ := id

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``DFunlike.coeFun
    (some { numArgs := 5, coercee := 4, type := .coeFun })

namespace DFunlike

variable [DFunlike F α β]

public protected theorem ext (f g : F) (h : ∀ x : α, f x = g x) : f = g := DFunlike.coeInj (funext h)

public protected theorem congrFun {f g : F} (h₁ : f = g) (x : α) : f x = g x := congrFun (congrArg _ h₁) x

end DFunlike

public theorem Function.hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀a, β a} {f' : ∀a, β' a}
    (hα : α = α') (h : ∀a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα
  have : ∀a, HEq (f a) (f' a) := fun a ↦ h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)
