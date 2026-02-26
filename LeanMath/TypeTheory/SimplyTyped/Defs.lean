import LeanMath.TypeTheory.Defs

namespace TypeTheory.SimplyTyped

inductive Ty where
 -- a term with no values. This only exists so that `Ty` has elemnts
| void
 -- the type of functions from arg to ret
| func (arg ret: Ty)

inductive IsWellTyped : List Ty -> Term -> Ty -> Prop where
| var (ctx: List Ty) (index: Nat) (h: index < ctx.length) :
  IsWellTyped ctx (.var index) ctx[index]
| lam (ctx: List Ty) (body: Term) (arg_ty ret_ty: Ty) :
  IsWellTyped (arg_ty::ctx) body ret_ty ->
  IsWellTyped ctx body.lam (arg_ty.func ret_ty)
| app (ctx: List Ty) (func arg: Term) (arg_ty ret_ty: Ty) :
  IsWellTyped ctx func (arg_ty.func ret_ty) ->
  IsWellTyped ctx arg arg_ty ->
  IsWellTyped ctx (.app func arg) ret_ty

namespace IsWellTyped

def weaken_at
  (ctx: List Ty) (ctx_ty ty: Ty) (pos: Nat) (h: pos ≤ ctx.length)
  (term: Term) : IsWellTyped ctx term ty ->
  IsWellTyped (ctx.insertIdx pos ctx_ty) (term.weaken pos) ty := by
  intro wt
  induction wt generalizing ctx_ty pos with
  | var ctx index index_lt =>
    rcases Nat.lt_or_ge index pos with g | g
    · rw [Term.weaken_var_lt _ _ g]
      rw [←List.getElem_insertIdx_of_lt]
      apply IsWellTyped.var
      assumption
      rw [List.length_insertIdx_of_le_length h]
      omega
    · rw [Term.weaken_var_ge _ _ g]
      rw [show ctx[index] = ctx[index + 1 - 1] from rfl]
      rw [←List.getElem_insertIdx_of_gt]
      apply IsWellTyped.var
      omega
      rw [List.length_insertIdx_of_le_length h]
      omega
  | lam ctx body arg_ty ret_ty wt ih =>
    apply IsWellTyped.lam
    rw [←List.insertIdx_succ_cons]
    apply ih
    dsimp; omega
  | app ctx func arg arg_ty ret_ty wtf wfa ihf iha =>
    apply IsWellTyped.app
    apply ihf
    assumption
    apply iha
    assumption

def weaken (ctx: List Ty) (ctx_ty ty: Ty) (term: Term) :
  IsWellTyped ctx term ty -> IsWellTyped (ctx_ty::ctx) term.weaken ty := by
  apply weaken_at (pos := 0)
  apply Nat.zero_le

def subst_at
  (ctx: List Ty) (ty: Ty) (pos: Nat) (h: pos < ctx.length)
  (term subst: Term) : IsWellTyped ctx term ty ->
  IsWellTyped (ctx.eraseIdx pos) subst ctx[pos] ->
  IsWellTyped (ctx.eraseIdx pos) (term.subst pos subst) ty := by
  intro wt swt
  induction wt generalizing pos subst with
  | var ctx index =>
    rcases Nat.lt_trichotomy index pos with g | rfl | g
    · rw [Term.subst_var_lt _ _ g]
      rw [←List.getElem_eraseIdx_of_lt]
      apply IsWellTyped.var
      rw [List.length_eraseIdx_of_lt h]
      omega
      assumption
    · rwa [Term.subst_var_eq]
    · rw [Term.subst_var_gt _ _ g]
      rw [show ctx[index] = ctx[index - 1 + 1] by
        congr; omega]
      rw [←List.getElem_eraseIdx_of_ge]
      apply IsWellTyped.var
      rw [List.length_eraseIdx_of_lt h]
      omega
      omega
  | lam ctx body arg_ty ret_ty wt ih =>
    apply IsWellTyped.lam
    rw [←List.eraseIdx_cons_succ]
    apply ih
    apply weaken
    assumption
    dsimp; omega
  | app ctx func arg arg_ty ret_ty wtf wta ihf iha =>
    apply IsWellTyped.app
    apply ihf
    assumption
    apply iha
    assumption

def subst (ctx: List Ty) (subst_ty ty: Ty) (term subst: Term) :
  IsWellTyped (subst_ty::ctx) term ty ->
  IsWellTyped ctx subst subst_ty ->
  IsWellTyped ctx (term.subst 0 subst) ty := by
  apply subst_at (pos := 0)
  apply Nat.zero_lt_succ

def beta (red: Term.Beta a b) :
  IsWellTyped ctx a ty -> IsWellTyped ctx b ty := by
  intro wt
  induction red generalizing ctx ty with
  | Lam body body' red ih =>
    cases wt with | lam ctx body arg_ty ret_ty wt =>
    apply IsWellTyped.lam
    apply ih
    assumption
  | AppFunc _ _ _ _ ih =>
    cases wt with | app _ _ _ _ _ =>
    apply IsWellTyped.app
    apply ih
    assumption
    assumption
  | AppArg _ _ _ _ ih =>
    cases wt with | app _ _ _ _ _ =>
    apply IsWellTyped.app
    assumption
    apply ih
    assumption
  | Subst =>
    cases wt with | app _ _ _ _ _ wt arg_wt =>
    cases wt with | lam =>
    apply subst
    assumption
    assumption

def beta_reduction (red: Term.BetaReduction a b) :
  IsWellTyped ctx a ty -> IsWellTyped ctx b ty := by
  intro wt
  induction red generalizing ctx ty with
  | refl => assumption
  | cons _ _ _ _ _ ih =>
    apply ih
    apply beta
    assumption
    assumption

end IsWellTyped

end TypeTheory.SimplyTyped
