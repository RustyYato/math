namespace TypeTheory

-- a term in untyped lambda calculus
inductive Term where
| var (index: Nat)
| lam (body: Term)
| app (func arg: Term)
deriving Repr, DecidableEq

namespace Term

def weaken (pos: Nat := 0) : Term -> Term
| .var index => .var <| if index < pos then index else index + 1
| .lam body => .lam <| body.weaken (pos + 1)
| .app func arg => .app (func.weaken pos) (arg.weaken pos)

private def subst_at (pos: Nat) (subst: Term) : Term -> Term
| .var index => if index = pos then subst else .var <| if index < pos then index else index - 1
| .lam body => .lam (subst_at (pos + 1) subst.weaken body)
| .app func arg => .app (subst_at pos subst func) (subst_at pos subst arg)

def subst (pos: Nat) (term subst: Term) := subst_at pos subst term

def subst_var_eq (index: Nat) (s: Term) : subst index (.var index) s = s := by
  rw [subst, subst_at, if_pos rfl]
def subst_var_lt (pos index: Nat) (h: index < pos) (s: Term) : subst pos (.var index) s = .var index := by
  rw [subst, subst_at, if_neg, if_pos h]
  apply Nat.ne_of_lt
  assumption
def subst_var_gt (pos index: Nat) (h: index > pos) (s: Term) : subst pos (.var index) s = .var (index - 1) := by
  rw [subst, subst_at, if_neg, if_neg]
  apply Nat.not_lt_of_lt
  assumption
  apply Nat.ne_of_gt
  assumption

@[simp] def subst_lam (pos: Nat) (body s: Term) : body.lam.subst pos s = (body.subst (pos + 1) s.weaken).lam := rfl
@[simp] def subst_app (pos: Nat) (func arg s: Term) : (func.app arg).subst pos s = (func.subst pos s).app (arg.subst pos s) := rfl

def weaken_var_lt (pos index: Nat) (h: index < pos) : weaken pos (.var index) = .var index := by simp [weaken, h]
def weaken_var_ge (pos index: Nat) (h: index ≥ pos) : weaken pos (.var index) = .var (index + 1) := by simp [weaken, h]

@[simp] def weaken_lam (pos: Nat) (body: Term) : body.lam.weaken pos = (body.weaken (pos + 1)).lam := rfl
@[simp] def weaken_app (pos: Nat) (func arg: Term) : (func.app arg).weaken pos = (func.weaken pos).app (arg.weaken pos) := rfl

-- a single step of beta reduction
inductive Beta : Term -> Term -> Type where
| Subst (body arg: Term) : Beta (.app body.lam arg) (body.subst 0 arg)
| Lam (body body': Term) : Beta body body' -> Beta body.lam body'.lam
| AppFunc (func func' arg: Term) : Beta func func' -> Beta (func.app arg) (func'.app arg)
| AppArg (func arg arg': Term) : Beta arg arg' -> Beta (func.app arg) (func.app arg')

inductive BetaReduction : Term -> Term -> Prop where
| refl (t: Term) : BetaReduction t t
| cons (a b c: Term) : Beta a b -> BetaReduction b c -> BetaReduction a c

inductive BetaEquiv : Term -> Term -> Prop where
| of (a b: Term) : Beta a b -> BetaEquiv a b
| refl (t: Term) : BetaEquiv t t
| symm (a b: Term) : BetaEquiv a b -> BetaEquiv b a
| trans (a b c: Term) : BetaEquiv a b -> BetaEquiv b c -> BetaEquiv a c

inductive Normalizing : Term -> Prop where
| norm (a: Term) : (∀b, Beta a b -> Normalizing b) -> Normalizing a

def Normalizing.acc : Normalizing a ↔ Acc (fun a b => Nonempty (Beta b a)) a := by
  apply Iff.intro
  · intro h
    induction h with
    | norm a h ih =>
    apply Acc.intro
    intro y ⟨hy⟩
    apply ih
    assumption
  · intro h
    induction h with
    | _ a h ih =>
    apply Normalizing.norm
    intro b h
    apply ih
    exact ⟨h⟩

def BetaReduction.Lam : BetaReduction a b ->BetaReduction a.lam b.lam
| .refl _ => .refl _
| .cons _ _ _ ab bc => .cons _ _ _ ab.Lam bc.Lam

def BetaReduction.AppFunc : BetaReduction a b ->BetaReduction (a.app x) (b.app x)
| .refl _ => .refl _
| .cons _ _ _ ab bc => .cons _ _ _ (ab.AppFunc _ _ _) bc.AppFunc

def BetaReduction.AppArg {x: Term} : BetaReduction a b ->BetaReduction (x.app a) (x.app b)
| .refl _ => .refl _
| .cons _ _ _ ab bc => .cons _ _ _ (ab.AppArg _ _ _) bc.AppArg

def BetaReduction.trans : BetaReduction a b -> BetaReduction b c -> BetaReduction a c := by
  intro h g
  induction h generalizing c with
  | refl => assumption
  | cons _ _ _ _ _ ih =>
    apply BetaReduction.cons
    assumption
    apply ih
    assumption

def weaken_comm (a: Term) (n m: Nat) (h: n ≤ m) : weaken n (weaken m a) = weaken (m + 1) (weaken n a) := by
  induction a generalizing n m with
  | lam body ih =>
    simp [weaken]
    apply ih
    omega
  | app func arg ihf iha =>
    simp [weaken]
    apply And.intro
    apply ihf
    assumption
    apply iha
    assumption
  | var index =>
    simp [weaken]
    by_cases h₀:index < m
    simp [h₀]
    split <;> omega
    simp [h₀]
    by_cases h₁:index < n
    simp [h₁]
    split
    split
    · exfalso
      omega
    · rfl
    · exfalso
      omega
    · rw [if_neg, if_neg, if_neg]
      any_goals omega
      rw [if_neg]
      omega
      omega

def subst_weaken_eq_weaken_subst (a b: Term) (n m: Nat) (h: m ≤ n) : subst m (weaken (n + 1) a) (weaken n b) = weaken n (subst m a b) := by
  induction a generalizing b n m with
  | var index =>
    dsimp [weaken]
    split <;> rename_i g
    · rcases Nat.lt_trichotomy index m with h' | rfl | h'
      · rw [subst_var_lt, subst_var_lt, weaken, if_pos]
        repeat omega
      · rw [subst_var_eq, subst_var_eq]
      · rw [subst_var_gt, subst_var_gt]
        dsimp [weaken]
        rw [if_pos]
        repeat omega
    · have : m < index := by omega
      rw [subst_var_gt, subst_var_gt]
      rw [weaken, if_neg]
      congr
      repeat omega
  | lam body ih =>
    simp
    rw [weaken_comm _ 0]
    apply ih
    omega
    apply Nat.zero_le
  | app func arg ihf iha =>
    simp; apply And.intro
    apply ihf
    assumption
    apply iha
    assumption

def subst_weaken_eq_weaken_subst' (a b: Term) (n m: Nat) (h: m ≥ n) :
  weaken n (subst m a b) = subst (m + 1) (weaken n a) (weaken n b) := by
  induction a generalizing b n m with
  | var index =>
    rcases Nat.lt_trichotomy index n with g | rfl | g
    · rw [subst_var_lt ,weaken_var_lt, subst_var_lt]
      repeat omega
    · rw [weaken_var_ge _ _ (by omega)]
      rcases Nat.lt_or_eq_of_le h with h | rfl
      · rw [subst_var_lt _ _ h, subst_var_lt _ _ (Nat.succ_lt_succ h), weaken_var_ge]
        apply Nat.le_refl
      · rw [subst_var_eq, subst_var_eq]
    · rw [weaken_var_ge _ _ (Nat.le_of_lt g)]
      rcases Nat.lt_trichotomy index m with h' | rfl | h'
      · rw [subst_var_lt _ _ h', subst_var_lt _ _ (Nat.succ_lt_succ h'),
          weaken_var_ge]
        omega
      · rw [subst_var_eq, subst_var_eq]
      · rw [subst_var_gt _ _ h', subst_var_gt _ _ (Nat.succ_lt_succ h'), weaken_var_ge]
        congr; omega
        omega
  | lam body ih =>
    simp
    rw [weaken_comm _ 0]
    apply ih
    omega
    apply Nat.zero_le
  | app func arg ihf iha =>
    simp; apply And.intro
    apply ihf
    assumption
    apply iha
    assumption

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

def subst_weaken_cancel (term: Term) (n: Nat) : subst n (weaken n term) x = term := by
  induction term generalizing n x with
  | lam body ih =>
    simp; apply ih
  | app func arg ihf iha =>
    simp; apply And.intro
    apply ihf
    apply iha
  | var index =>
    rcases Nat.lt_or_ge index n with h | h
    rw [weaken_var_lt _ _ h, subst_var_lt _ _ h]
    rw [weaken_var_ge _ _ h, subst_var_gt _ _ (Nat.lt_succ_of_le h)]
    rfl

def subst_comm (body arg arg': Term) (h: n ≤ m) : subst n (subst (m + 1) body (weaken n arg)) (subst m arg' arg) = subst m (subst n body arg') arg := by
  induction body generalizing n m arg arg' with
  | lam body ih =>
    simp
    rw [weaken_comm _ 0]
    rw [←ih (n := n + 1) (m := m + 1) (arg := weaken 0 arg) (arg' := weaken 0 arg') (by omega)]
    congr
    · clear ih h n
      rw [←subst_weaken_eq_weaken_subst']
      apply Nat.zero_le
    apply Nat.zero_le
  | app func₀ arg₀ ihf iha =>
    simp
    apply And.intro
    apply ihf
    assumption
    apply iha
    assumption
  | var index =>
    rcases Nat.lt_trichotomy index n with g | rfl | g
    · rw [subst_var_lt, subst_var_lt _ _ g, subst_var_lt _ _ g, subst_var_lt]
      repeat omega
    · rw [subst_var_lt _ _ (by omega), subst_var_eq ,subst_var_eq]
    · rw [subst_var_gt _ _ g]
      match index with
      | index + 1 =>
      dsimp
      rcases Nat.lt_trichotomy index m with g' | rfl | g'
      · rw [subst_var_lt _ _ g', subst_var_lt _ _ (Nat.succ_lt_succ g'),
          subst_var_gt _ _ g]
        rfl
      · rw [subst_var_eq, subst_var_eq, subst_weaken_cancel]
      · rw [subst_var_gt _ _ (Nat.succ_lt_succ g'),
        subst_var_gt, subst_var_gt _ _ g']
        rfl
        omega

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

def strongConfluence {a b c: Term} (ab: Beta a b) (ac: Beta a c) : ∃d, b.BetaReduction d ∧ c.BetaReduction d := by
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

end Term

end TypeTheory
