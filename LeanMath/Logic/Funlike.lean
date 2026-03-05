import LeanMath.Tactic.TypeStar

class DFunLike (F: Sort*) (α: outParam Sort*) (β: outParam (α -> Sort*)) where
  coeFun (f: F) (a: α) : β a := by intro f; exact f.toFun
  coeInj: Function.Injective coeFun := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply DFunLike.coeInj
      assumption

abbrev FunLike (F: Sort*) (α β: Sort*) := DFunLike F α (fun _ => β)
abbrev RelLike (F: Sort*) (α: Sort*) := FunLike F α (α -> Prop)

instance [DFunLike F α β] : CoeFun F (fun _ => ∀x, β x) where
  coe := DFunLike.coeFun

instance {α: Sort*} {β: α -> Sort*} : DFunLike (∀x: α, β x) α β where
  coeFun := id
  coeInj _ _ := id

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``DFunLike.coeFun
    (some { numArgs := 5, coercee := 4, type := .coeFun })

namespace DFunLike

variable [DFunLike F α β]

protected def ext (f g : F) (h : ∀ x : α, f x = g x) : f = g := DFunLike.coeInj (funext h)

protected theorem congrFun {f g : F} (h₁ : f = g) (x : α) : f x = g x := congrFun (congrArg _ h₁) x

end DFunLike

def Function.hfunext {α α' : Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : ∀a, β a} {f' : ∀a, β' a}
    (hα : α = α') (h : ∀a a', HEq a a' → HEq (f a) (f' a')) : HEq f f' := by
  subst hα
  have : ∀a, HEq (f a) (f' a) := fun a ↦ h a a (HEq.refl a)
  have : β = β' := by funext a; exact type_eq_of_heq (this a)
  subst this
  apply heq_of_eq
  funext a
  exact eq_of_heq (this a)
