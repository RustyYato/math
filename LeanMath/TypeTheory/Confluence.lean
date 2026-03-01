import LeanMath.TypeTheory.Defs
import LeanMath.Logic.Relation.ChurchRosser

namespace TypeTheory.Term

private inductive ParallelBeta : Term -> Term -> Prop where
| refl (t: Term) : ParallelBeta t t
| Lam (body body': Term) :
  ParallelBeta body body' ->
  ParallelBeta body.lam body'.lam
| App (func func' arg arg': Term) :
  ParallelBeta func func' ->
  ParallelBeta arg arg' ->
  ParallelBeta (func.app arg) (func'.app arg')
| Subst (body body' arg arg': Term) :
  ParallelBeta body body' ->
  ParallelBeta arg arg' ->
  ParallelBeta (.app body.lam arg) (body'.subst 0 arg')

private def ParallelBetaReduction :=
  Relation.ReflTransGen ParallelBeta

private inductive ParallelBetaReductionChain : Term -> Term -> Type where
| refl (t: Term) : ParallelBetaReductionChain t t
| cons (a b c: Term) : ParallelBeta a b -> ParallelBetaReductionChain b c -> ParallelBetaReductionChain a c

private def ParallelBetaReductionChain.length : ParallelBetaReductionChain a b -> Nat
| .refl _ => 0
| .cons _ _ _ _ h => h.length + 1

private def ParallelBetaReductionChain.trans : ParallelBetaReductionChain a b -> ParallelBetaReductionChain b c -> ParallelBetaReductionChain a c
| .refl _, x => x
| .cons _ _ _ h g, x => .cons _ _ _ h (g.trans x)

private def ParallelBetaReductionChain.of : ParallelBeta a b -> ParallelBetaReductionChain a b :=
  fun x => .cons _ _ _ x (.refl _)

def weaken_beta (term term': Term) (n: Nat) (h: term.Beta term') : Nonempty ((weaken n term).Beta (weaken n term')) := by
  induction h generalizing n with
  | Lam _ _ _ ih =>
    have ⟨ih⟩ := ih (n + 1)
    exact ⟨ih.Lam⟩
  | AppFunc _ _ _ _ ih =>
    have ⟨ih⟩ := ih n
    exact ⟨ih.AppFunc _ _ _⟩
  | AppArg _ _ _ _ ih =>
    have ⟨ih⟩ := ih n
    exact ⟨ih.AppArg _ _ _⟩
  | Subst body arg =>
    dsimp [weaken]
    rw [←subst_weaken_eq_weaken_subst]
    exact ⟨Beta.Subst _ _⟩
    apply Nat.zero_le

def subst_arg_beta (body arg arg': Term) (n: Nat) (h: arg.Beta arg') : (subst n body arg).BetaReduction (subst n body arg') := by
  induction body generalizing n arg arg' with
  | var index =>
    rcases Nat.lt_trichotomy index n with g | rfl | g
    · rw [subst_var_lt _ _ g, subst_var_lt _ _ g]
      apply BetaReduction.refl
    · rw [subst_var_eq, subst_var_eq]
      apply BetaReduction.cons
      assumption
      apply BetaReduction.refl
    · rw [subst_var_gt _ _ g, subst_var_gt _ _ g]
      apply BetaReduction.refl
  | lam body ih =>
    dsimp
    apply BetaReduction.Lam
    have ⟨h⟩  := weaken_beta _ _ 0 h
    apply ih
    assumption
  | app func arg₀ ihf iha =>
    dsimp
    apply BetaReduction.trans
    apply BetaReduction.AppFunc
    apply ihf
    assumption
    apply BetaReduction.AppArg
    apply iha
    assumption

def subst_body_beta (body body' arg: Term) (n: Nat) (h: body.Beta body') : (subst n body arg).BetaReduction (subst n body' arg) := by
  induction h generalizing n arg with
  | Lam body body' h ih =>
    apply BetaReduction.Lam
    apply ih
  | AppFunc _ _ _ _ ih =>
    apply BetaReduction.AppFunc
    apply ih
  | AppArg _ _ _ _ ih =>
    apply BetaReduction.AppArg
    apply ih
  | Subst body arg' =>
    rename_i b; clear b
    dsimp
    rw [←subst_comm]
    apply BetaReduction.cons
    apply Beta.Subst
    apply BetaReduction.refl
    apply Nat.zero_le

def subst_arg_beta_reduction (body arg arg': Term) (n: Nat) (h: arg.BetaReduction arg') : (subst n body arg).BetaReduction (subst n body arg') := by
  induction h with
  | refl => exact .refl _
  | cons _ _ _ _ _ ih =>
    apply BetaReduction.trans
    apply subst_arg_beta
    assumption
    assumption

def subst_body_beta_reduction (body body' arg: Term) (n: Nat) (h: body.BetaReduction body') : (subst n body arg).BetaReduction (subst n body' arg) := by
  induction h with
  | refl => exact .refl _
  | cons _ _ _ _ _ ih =>
    apply BetaReduction.trans
    apply subst_body_beta
    assumption
    assumption

private def weaken_par_beta (term term': Term) (n: Nat) (h: term.ParallelBeta term') : (weaken n term).ParallelBeta (weaken n term') := by
  induction h generalizing n with
  | refl => apply ParallelBeta.refl
  | Lam _ _ _ ih => exact (ih (n + 1)).Lam
  | App _ _ _ _ _ _ ihf iha =>
    apply ParallelBeta.App
    apply ihf
    apply iha
  | Subst body arg arg' h _ _ ihb iha =>
    dsimp [weaken]
    rw [←subst_weaken_eq_weaken_subst]
    apply ParallelBeta.Subst _ _
    apply ihb
    apply iha
    apply Nat.zero_le

private def subst_arg_par_beta (body arg arg': Term) (n: Nat) (h: arg.ParallelBeta arg') : (subst n body arg).ParallelBeta (subst n body arg') := by
  induction body generalizing n arg arg' with
  | var index =>
    rcases Nat.lt_trichotomy index n with g | rfl | g
    · rw [subst_var_lt _ _ g, subst_var_lt _ _ g]
      apply ParallelBeta.refl
    · rw [subst_var_eq, subst_var_eq]
      assumption
    · rw [subst_var_gt _ _ g, subst_var_gt _ _ g]
      apply ParallelBeta.refl
  | lam body ih =>
    dsimp
    apply ParallelBeta.Lam
    apply ih
    exact weaken_par_beta _ _ 0 h
  | app func arg₀ ihf iha =>
    dsimp
    apply ParallelBeta.App
    apply ihf
    assumption
    apply iha
    assumption

private def subst_body_par_beta (body body' arg: Term) (n: Nat) (h: body.ParallelBeta body') : (subst n body arg).ParallelBeta (subst n body' arg) := by
  induction h generalizing n arg with
  | refl => apply ParallelBeta.refl
  | Lam body body' h ih =>
    apply ParallelBeta.Lam
    apply ih
  | App _ _ _ _ _ _ ihf iha =>
    apply ParallelBeta.App
    apply ihf
    apply iha
  | Subst body arg' arg'' _ _ _ ihb iha =>
    rename_i b; clear b
    dsimp
    rw [←subst_comm]
    apply ParallelBeta.Subst
    apply ihb
    apply iha
    apply Nat.zero_le

private def subst_par_beta (body body' arg arg': Term) (n: Nat) (h: body.ParallelBeta body') (g: arg.ParallelBeta arg') : (subst n body arg).ParallelBeta (subst n body' arg') := by
  induction h generalizing n arg arg' with
  | refl =>
    apply subst_arg_par_beta
    assumption
  | Lam body body' h ih =>
    dsimp
    apply ParallelBeta.Lam
    apply ih
    apply weaken_par_beta
    assumption
  | App _ _ _ _ _ _ ihf iha =>
    apply ParallelBeta.App
    apply ihf
    assumption
    apply iha
    assumption
  | Subst body arg₀ arg₀' h _ _ ihb iha =>
    rename_i b; clear b
    dsimp
    rw [←subst_comm _ _ _ (Nat.zero_le _)]
    apply ParallelBeta.Subst
    apply ihb
    apply weaken_par_beta
    assumption
    apply iha
    assumption

private def ParallelBeta.ofBeta : Beta a b -> ParallelBeta a b
| .Subst body arg => .Subst _ _ _ _ (.refl _) (.refl _)
| .AppArg func arg arg' h => .App _ _ _ _ (.refl _) (.ofBeta h)
| .AppFunc func arg arg' h => .App _ _ _ _ (.ofBeta h) (.refl _)
| .Lam body body' h => .Lam _ _ (.ofBeta h)

private def BetaReduction.ofParallel : ParallelBeta a b -> BetaReduction a b := by
  intro h
  induction h with
  | refl => apply BetaReduction.refl
  | Lam body body' h ih =>
    apply BetaReduction.Lam
    assumption
  | App func func' arg arg' _ _ ihf iha =>
    apply BetaReduction.trans
    apply BetaReduction.AppFunc
    assumption
    apply BetaReduction.AppArg
    assumption
  | Subst =>
    apply BetaReduction.trans
    apply BetaReduction.cons
    apply Beta.Subst
    apply BetaReduction.refl
    apply BetaReduction.trans
    apply subst_arg_beta_reduction
    assumption
    apply subst_body_beta_reduction
    assumption

private def BetaReduction.ofParallelReduction : ParallelBetaReduction a b -> BetaReduction a b := by
  intro h
  induction h with
  | refl => apply BetaReduction.refl
  | cons a b c ab bc ih =>
    apply BetaReduction.trans _ ih
    apply ofParallel
    assumption

private def BetaReduction.toParallelReduction : BetaReduction a b -> ParallelBetaReduction a b := by
  intro h
  induction h with
  | refl => apply Relation.ReflTransGen.refl
  | cons a b c ab bc ih =>
    apply Relation.ReflTransGen.cons
    exact ParallelBeta.ofBeta ab
    assumption

private def ParallelBetaReduction.iffChain : ParallelBetaReduction a b ↔ Nonempty (ParallelBetaReductionChain a b) := by
  apply Iff.intro
  · intro h
    induction h with
    | refl => exact ⟨.refl _⟩
    | cons a b c h g ih =>
      obtain ⟨ih⟩ := ih
      refine ⟨?_⟩
      apply ParallelBetaReductionChain.cons
      assumption
      assumption
  · intro ⟨h⟩
    induction h with
    | refl => exact .refl _
    | cons a b c h g ih =>
      apply Relation.ReflTransGen.cons
      assumption
      assumption

def weakConfluence {a b c: Term} (ab: Beta a b) (ac: Beta a c) : ∃d, b.BetaReduction d ∧ c.BetaReduction d := by
  induction ab generalizing c with
  | Subst body arg =>
    cases ac with
    | Subst => exact ⟨_, .refl _, .refl _⟩
    | AppFunc func func' arg h =>
      cases h with | Lam body body' h =>
      refine ⟨_, ?_, .cons _ _ _ (.Subst _ _) (.refl _)⟩
      apply subst_body_beta
      assumption
    | AppArg func arg arg' h =>
      refine ⟨_, ?_, .cons _ _ _ (.Subst _ _) (.refl _)⟩
      apply subst_arg_beta
      assumption
  | Lam body body' h ih =>
    cases ac with | Lam _ body'' g =>
    replace ⟨d, l, r⟩ := ih g
    exact ⟨_, l.Lam, r.Lam⟩
  | AppFunc func func' arg h ih =>
    cases ac with
    | Subst =>
      cases h with | Lam =>
      refine ⟨_, .cons _ _ _ (.Subst _ _) (.refl _), ?_⟩
      apply subst_body_beta
      assumption
    | AppFunc func func'' arg g =>
      have ⟨d, l, r⟩ := ih g
      exact ⟨_, l.AppFunc, r.AppFunc⟩
    | AppArg func arg arg' g =>
      exact ⟨_, .cons _ _ _ (.AppArg _ _ _ g) (.refl _), .cons _ _ _ (.AppFunc _ _ _ h) (.refl _)⟩
  | AppArg func arg arg' h ih =>
    cases ac with
    | Subst body =>
      refine ⟨_, .cons _ _ _ (.Subst _ _) (.refl _), ?_⟩
      apply subst_arg_beta
      assumption
    | AppFunc func func'' arg g =>
      exact ⟨_, .cons _ _ _ (.AppFunc _ _ _ g) (.refl _), .cons _ _ _ (.AppArg _ _ _ h) (.refl _)⟩
    | AppArg func arg arg' g =>
      have ⟨d, l, r⟩ := ih g
      exact ⟨_, l.AppArg, r.AppArg⟩

private def parallelStrongConfluence {a b c: Term} (ab: ParallelBeta a b) (ac: ParallelBeta a c) : ∃d, ParallelBeta b d ∧ ParallelBeta c d := by
  induction ab generalizing c with
  | refl =>
    exists c
    apply And.intro
    assumption
    apply ParallelBeta.refl
  | Lam body body' h ih =>
    cases ac with
    | refl =>
      exists body'.lam
      apply And.intro
      apply ParallelBeta.refl
      apply ParallelBeta.Lam
      assumption
    | Lam _ _ ac =>
    have ⟨body'', l, r⟩ := ih ac
    exists body''.lam
    apply And.intro
    apply l.Lam
    apply r.Lam
  | App func func' arg arg' h g ihf iha =>
    cases ac with
    | refl => exact ⟨.app func' arg', .refl _, .App _ _ _ _ h g⟩
    | App func₀ func₀' arg₀ arg₀' h g =>
      have ⟨func₁, l₁, r₁⟩ := ihf h
      have ⟨arg₁, l₂, r₂⟩ := iha g
      exact ⟨_, .App _ _ _ _ l₁ l₂, .App _ _ _ _ r₁ r₂⟩
    | Subst body body' _ arg₀ hbody harg =>
      have ⟨arg₀', l, r⟩ := iha harg
      cases h with
      | refl =>
        refine ⟨body'.subst 0 arg₀', ?_, ?_⟩
        · apply ParallelBeta.Subst
          assumption
          assumption
        · apply subst_arg_par_beta
          assumption
      | Lam body body₀ h =>
        have ⟨x, lx, rx⟩ := ihf hbody.Lam
        cases lx with
        | refl =>
          refine ⟨_, .Subst _ _ _ _ (.refl _) l, ?_⟩
          apply subst_par_beta
          · cases rx
            apply ParallelBeta.refl
            assumption
          assumption
        | Lam _ _ lx =>
        refine ⟨_, .Subst _ _ _ _ lx l, ?_⟩
        apply subst_par_beta
        · cases rx
          apply ParallelBeta.refl
          assumption
        assumption
  | Subst body body' arg arg' hbody harg ihb iha =>
    cases ac with
    | refl =>
      refine ⟨_, .refl _, ?_⟩
      apply ParallelBeta.Subst
      assumption
      assumption
    | Subst _ body₀ _ arg₀ hbody₀ harg₀ =>
      have ⟨b₁, lb, rb⟩ := ihb hbody₀
      have ⟨a₁, la, ra⟩ := iha harg₀
      refine ⟨_, subst_par_beta _ _ _ _ _ lb la, ?_⟩
      apply subst_par_beta
      assumption
      assumption
    | App func func' arg arg' hf ha =>
      have ⟨a₁, la, ra⟩ := iha ha
      cases hf with
      | refl =>
        refine ⟨_, subst_par_beta _ _ _ _ _ (.refl _) la, ?_⟩
        apply ParallelBeta.Subst
        assumption
        assumption
      | Lam body body' h =>
        have ⟨b₁, lb, rb⟩ := ihb h
        refine ⟨_, ?_, .Subst _ _ _ _ rb ra⟩
        apply subst_par_beta
        assumption
        assumption

def confluence {a b c: Term} (ab: BetaReduction a b) (ac: BetaReduction a c) : ∃d, b.BetaReduction d ∧ c.BetaReduction d := by
  replace ab := BetaReduction.toParallelReduction ab
  replace ac := BetaReduction.toParallelReduction ac
  have ⟨d, l, r⟩ := Relation.church_rosser ?_ ab ac
  refine ⟨d, ?_, ?_⟩
  exact .ofParallelReduction l
  exact .ofParallelReduction r
  intro a b c ab ac
  have ⟨d, bd, cd⟩ := parallelStrongConfluence ab ac
  refine ⟨d, ?_, ?_⟩
  apply Relation.ReflGen.of
  assumption
  apply Relation.ReflTransGen.of
  assumption

end TypeTheory.Term
