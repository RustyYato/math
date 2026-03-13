import LeanMath.TypeTheory.SimplyTyped.Defs

namespace TypeTheory.SimplyTyped

def Halts (term: Term) := ∃val: Term, Relation.ReflTransGen Term.RestrictedBeta term val ∧ val.IsValue

def HeredHalts (term: Term) (wt: IsWellTyped ctx term ty) : Prop :=
  match ty with
  | .void => False
  | .func arg_ty _ret_ty =>
    term.Normalizing ∧
    ∀(arg: Term) (arg_wt: IsWellTyped ctx arg arg_ty),
      HeredHalts arg arg_wt ->
      HeredHalts (.app term arg) (.app _ _ _ _ _ wt arg_wt)

namespace HeredHalts

-- def beta (r: Term.Beta a b) (wt: IsWellTyped ctx a ty) :
--   HeredHalts a wt ↔ HeredHalts b (wt.beta r) := by
--   induction ty with
--   | void => apply Iff.intro id id
--   | func arg_ty ret_ty iha ihr =>
--     apply Iff.intro
--     · intro h
--       apply And.intro
--       apply h.left.apply
--       assumption
--       intro arg arg_wt
--       sorry
--     · intro h
--       apply And.intro
--       sorry
--       sorry

end HeredHalts

end TypeTheory.SimplyTyped
