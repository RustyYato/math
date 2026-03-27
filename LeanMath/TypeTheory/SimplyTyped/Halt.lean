import LeanMath.TypeTheory.SimplyTyped.Defs
import LeanMath.Tactic.AxiomBlame

namespace TypeTheory.SimplyTyped

def HeredHalts (term: Term) (wt: IsWellTyped ctx term ty) : Prop :=
  match ty with
  | .void => False
  | .func arg_ty _ret_ty =>
    term.Halts ∧
    ∀(arg: Term) (arg_wt: IsWellTyped ctx arg arg_ty),
      HeredHalts arg arg_wt ->
      HeredHalts (.app term arg) (.app _ _ _ _ _ wt arg_wt)

private inductive IsWellTypedEmptyCtx : Term -> Ty -> Prop where
| lam (body: Term) (arg_ty ret_ty: Ty) :
  IsWellTyped [] body.lam (arg_ty.func ret_ty) ->
  IsWellTypedEmptyCtx body.lam (arg_ty.func ret_ty)
| app (func arg: Term) (ret_ty: Ty) :
  IsWellTyped [] (.app func arg) ret_ty ->
  IsWellTypedEmptyCtx (.app func arg) ret_ty

inductive HeredHalts.SubstAll : List Ty -> List Term -> Prop where
| nil : SubstAll [] []
| cons (wt: IsWellTyped [] arg arg_ty) :
  HeredHalts arg wt ->
  SubstAll ctx substs ->
  SubstAll (arg_ty::ctx) (arg::substs)

namespace Halts

def beta {a b ty} (r: Term.RestrictedBeta a b) (wt: IsWellTyped ctx a ty) : a.Halts ↔ b.Halts := by
  induction r with
  | Subst =>
    apply Iff.intro
    · intro ⟨v, h, hval⟩
      cases h
      contradiction
      rename_i h _
      cases h
      exists v
      contradiction
      rename_i h _; have := h.NotValue
      contradiction
    · intro ⟨v, h, hval⟩
      refine ⟨v, ?_, hval⟩
      apply Relation.ReflTransGen.cons
      apply Term.RestrictedBeta.Subst
      assumption
      assumption
  | AppFunc func func' arg beta ih =>
    apply Iff.intro
    · intro ⟨v, h, hval⟩
      refine ⟨v, ?_, hval⟩
      cases h
      contradiction
      rename_i h _; cases h
      contradiction
      rename_i h _; cases beta.unique h
      assumption
      have := beta.NotValue
      contradiction
    · intro ⟨v, h, hval⟩
      refine ⟨v, ?_, hval⟩
      apply Relation.ReflTransGen.cons
      apply Term.RestrictedBeta.AppFunc
      assumption
      assumption
  | AppArg =>
    apply Iff.intro
    · intro ⟨v, h, hval⟩
      refine ⟨v, ?_, hval⟩
      rename_i beta _
      cases h
      contradiction
      rename_i h _; cases h
      have := beta.NotValue
      contradiction
      rename_i h _
      have := h.NotValue
      contradiction
      rename_i h _
      cases beta.unique h
      assumption
    · intro ⟨v, h, hval⟩
      refine ⟨v, ?_, hval⟩
      apply Relation.ReflTransGen.cons
      apply Term.RestrictedBeta.AppArg
      assumption
      assumption
      assumption

end Halts

namespace HeredHalts

protected def Halts : HeredHalts a wt -> a.Halts := by
  intro h; rename_i ty
  cases ty
  contradiction
  exact h.left

def beta {a b ty} (r: Term.RestrictedBeta a b) (wt: IsWellTyped ctx a ty) : HeredHalts a wt ↔ HeredHalts b (wt.beta r.Beta) := by
  induction ty generalizing a b with
  | void => apply Iff.intro id id
  | func arg_ty ret_ty iha ihr =>
    apply Iff.intro
    · intro h
      apply And.intro
      apply (Halts.beta r wt).mp h.left
      intro arg arg_wt arg_hhalts
      apply (ihr _ _).mp
      exact h.right arg arg_wt arg_hhalts
      apply Term.RestrictedBeta.AppFunc
      assumption
    · intro h
      apply And.intro
      apply (Halts.beta r wt).mpr h.left
      intro arg arg_wt arg_hhalts
      apply (ihr _ _).mpr
      exact h.right arg arg_wt arg_hhalts
      apply Term.RestrictedBeta.AppFunc
      assumption

def beta_star {a b ty} (r: Relation.ReflTransGen Term.RestrictedBeta a b) (wt: IsWellTyped ctx a ty) : HeredHalts a wt ↔ HeredHalts b (wt.rbeta_star r) := by
  induction r with
  | refl => rfl
  | cons a b c r bc ih =>
    apply Iff.trans
    apply beta
    assumption
    apply ih

def SubstAll.wf : HeredHalts.SubstAll ctx substs -> SimplyTyped.SubstAll ctx substs := by
  intro h
  induction h with
  | nil => apply SimplyTyped.SubstAll.nil
  | cons a ah ih =>
    apply SimplyTyped.SubstAll.cons <;> assumption

def SubstAll.getElem (h: HeredHalts.SubstAll ctx substs) : ∀(i: ℕ) (hi: i < ctx.length),
  HeredHalts (substs[i]'(h.wf.length_eq ▸ hi)) (h.wf.getElem i hi) := by
  intro i hi
  induction h generalizing i with
  | nil => contradiction
  | @cons arg arg_ty ctx args arg_wt arg_halts args_wt ih  =>
    cases i with
    | zero => assumption
    | succ i => apply ih

def subst_all (term: Term) (substs: List Term) (wf: IsWellTyped ctx term ty) (hsubst: HeredHalts.SubstAll ctx substs) : HeredHalts (term.subst_all 0 substs) (ctx := []) (ty := ty) (by
    rw [←List.append_nil []]
    apply IsWellTyped.subst_all
    exact hsubst.wf
    rwa [List.nil_append, List.append_nil]) := by
    induction wf generalizing substs with
    | app ctx func arg arg_ty ret_ty func_wt arg_wt ihf iha =>
      conv => { lhs; rw [Term.subst_all_app] }
      apply (ihf substs hsubst).right
      apply iha
      assumption
    | var =>
      have := hsubst.wf.length_eq
      conv => { lhs; rw [Term.subst_all_var _ hsubst.wf.closed _ (by omega)] }
      apply hsubst.getElem
    | lam ctx body arg_ty ret_ty wt ih =>
      conv => { lhs; rw [Term.subst_all_lam _ hsubst.wf.closed] }
      dsimp
      apply And.intro
      · exact ⟨_, Relation.ReflTransGen.refl _, Term.IsValue.lam _⟩
      · intro arg arg_wt arg_halts
        have ⟨arg', red, val⟩ := arg_halts.Halts
        apply (beta_star (b := (Term.subst_all 1 substs body ).lam.app arg') _ _).mpr
        apply (beta (Term.RestrictedBeta.Subst _ _ _) _).mpr
        · conv => { lhs; rw [Term.subst_all_comm_subst _ _ _ (by
            apply IsWellTyped.closed
            apply arg_wt.rbeta_star
            assumption
            apply Nat.le_refl) (by
            intro a ha
            apply hsubst.wf.closed
            assumption)] }
          show HeredHalts (Term.subst_all 0 (arg'::substs) body) _
          apply ih
          apply SubstAll.cons
          apply (HeredHalts.beta_star red _).mp
          assumption
          assumption
        · apply Term.RestrictedBeta.star_arg_arg
          apply Term.IsValue.lam
          assumption
        · assumption

def closed_wt (term: Term) (h: IsWellTyped [] term ty) : HeredHalts term h := subst_all term [] h HeredHalts.SubstAll.nil

end HeredHalts

def halts (term: Term) (h: IsWellTyped [] term ty) : term.Halts := (HeredHalts.closed_wt term h).Halts

end TypeTheory.SimplyTyped
