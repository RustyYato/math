import LeanMath.Tactic.TypeStar

class DFunLike (F: Type*) (α: outParam Sort*) (β: outParam (α -> Sort*)) where
  coeFun (f: F) (a: α) : β a := by intro f; exact f.toFun
  coeInj: Function.Injective coeFun := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply DFunLike.coeInj
      assumption

abbrev FunLike (F: Type*) (α β: Sort*) := DFunLike F α (fun _ => β)

instance [DFunLike F α β] : CoeFun F (fun _ => ∀x, β x) where
  coe := DFunLike.coeFun

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``DFunLike.coeFun
    (some { numArgs := 5, coercee := 4, type := .coeFun })

namespace DFunLike

variable [DFunLike F α β]

protected def ext (f g : F) (h : ∀ x : α, f x = g x) : f = g := DFunLike.coeInj (funext h)

protected theorem congrFun {f g : F} (h₁ : f = g) (x : α) : f x = g x := congrFun (congrArg _ h₁) x

end DFunLike
