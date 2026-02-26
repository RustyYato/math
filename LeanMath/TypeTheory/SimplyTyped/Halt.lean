import LeanMath.TypeTheory.SimplyTyped.Defs

namespace TypeTheory.SimplyTyped

def HeredHalts (term: Term) (wt: IsWellTyped ctx term ty) : Prop :=
  match ty with
  | .void => False
  | .func arg_ty _ret_ty =>
    term.Normalizing ∧
    ∀(arg: Term) (arg_wt: IsWellTyped ctx arg arg_ty),
      HeredHalts arg arg_wt ->
      HeredHalts (.app term arg) (.app _ _ _ _ _ wt arg_wt)

end TypeTheory.SimplyTyped
