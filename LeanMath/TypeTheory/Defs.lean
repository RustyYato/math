import LeanMath.Logic.Relation.Defs

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
deriving Repr

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

def BetaReduction.Lam : BetaReduction a b -> BetaReduction a.lam b.lam
| .refl _ => .refl _
| .cons _ _ _ ab bc => .cons _ _ _ ab.Lam bc.Lam

def BetaReduction.AppFunc : BetaReduction a b -> BetaReduction (a.app x) (b.app x)
| .refl _ => .refl _
| .cons _ _ _ ab bc => .cons _ _ _ (ab.AppFunc _ _ _) bc.AppFunc

def BetaReduction.AppArg {x: Term} : BetaReduction a b -> BetaReduction (x.app a) (x.app b)
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

inductive IsValue : Term -> Prop where
| lam (body: Term) : IsValue (.lam body)

instance : ∀a, Decidable (IsValue a)
| .lam _ => .isTrue (.lam _)
| .var _ | .app _ _ => .isFalse nofun

-- `IsClosed a pos` means that the term `a` only contains free variables
-- strictly smaller than `pos`. In particular, `IsClosed a 0` means
-- that the term `a` contains no free variables
inductive IsClosed : Term -> Nat -> Prop where
| var (pos index: Nat) : index < pos -> IsClosed (.var index) pos
| lam (pos: Nat) (body: Term) : IsClosed body (pos + 1) -> IsClosed (.lam body) pos
| app (pos: Nat) (func arg: Term) : IsClosed func pos -> IsClosed arg pos -> IsClosed (.app func arg) pos

def weaken_closed' (n m: Nat) (a: Term) (h: IsClosed a m) (g: m ≤ n) : weaken n a = a := by
  induction h generalizing n with
  | var _ index =>
    rcases Nat.lt_or_ge index n with g' | g'
    rw [weaken_var_lt _ _ g']
    omega
  | lam pos body _ ih =>
    dsimp; congr
    apply ih
    omega
  | app pos func arg _ _ ihf iha =>
    dsimp; congr
    apply ihf
    assumption
    apply iha
    assumption

def subst_closed' (n m: Nat) (a b: Term) (h: IsClosed a m) (g: m ≤ n) : subst n a b = a := by
  induction h generalizing n b with
  | var _ index =>
    rcases Nat.lt_or_ge index n with g' | g'
    rw [subst_var_lt _ _ g']
    omega
  | lam pos body _ ih =>
    dsimp; congr
    apply ih
    omega
  | app pos func arg _ _ ihf iha =>
    dsimp; congr
    apply ihf
    assumption
    apply iha
    assumption

def weaken_closed (a: Term) (h: IsClosed a 0) : weaken n a = a := by
  apply weaken_closed'
  assumption
  apply Nat.zero_le

def subst_closed (a b: Term) (h: IsClosed a 0) : subst n a b = a := by
  apply subst_closed'
  assumption
  apply Nat.zero_le

private def is_closed_at (n: Nat) : Term -> Bool
| .var index => index < n
| .app func arg => func.is_closed_at n && arg.is_closed_at n
| .lam body => body.is_closed_at (n + 1)

private def is_closed_at_spec (n: Nat) (a: Term) : a.is_closed_at n ↔ a.IsClosed n := by
  induction a generalizing n with
  | var index =>
    simp [is_closed_at]
    apply Iff.intro
    intro h
    apply IsClosed.var
    assumption
    intro (.var _ _ h)
    exact h
  | lam body ih =>
    apply (ih _).trans
    apply Iff.intro
    apply IsClosed.lam
    intro h; cases h
    assumption
  | app func arg ihf iha =>
    simp [is_closed_at]
    apply Iff.intro
    intro ⟨h ,g⟩
    apply IsClosed.app
    apply (ihf _).mp h
    apply (iha _).mp g
    intro h; cases h
    apply And.intro
    apply (ihf _).mpr
    assumption
    apply (iha _).mpr
    assumption

instance : Decidable (IsClosed a n) :=
  decidable_of_bool (is_closed_at n a) (is_closed_at_spec _ _)

-- the canonical next beta reduction of a closed non-value term
def Beta.canonical (a: Term) (h: IsClosed a 0) (g: ¬IsValue a) : Σb, Beta a b :=
  match a with
  | .lam _ => nomatch g (.lam _)
  | .app func arg =>
    if hv:func.IsValue then
      if ha:arg.IsValue then
        match func with
        | .lam body => ⟨_, Beta.Subst _ _⟩
      else
        have ⟨arg', h⟩ := Beta.canonical arg (by cases h; assumption) ha
        ⟨_, Beta.AppArg _ _ _ h⟩
    else
      have ⟨func', h⟩ := Beta.canonical func (by cases h; assumption) hv
      ⟨_, Beta.AppFunc _ _ _ h⟩

-- a simplest term where the canonical beta reduction equals itself
def Ω : Term  := .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))

def subst_all (n: Nat) (args: List Term) : Term -> Term :=
  args.foldl (subst n)

@[simp] def subst_all_nil : subst_all n [] term = term := rfl
@[simp] def subst_all_cons (arg: Term) (args: List Term) : subst_all n (arg::args) term = subst_all n args (term.subst n arg) := rfl

def susbt_all_closed (a: Term) (args: List Term) (h: IsClosed a 0) : subst_all n args a = a := by
  induction args with
  | nil => rfl
  | cons arg args ih => simp [ih, subst_closed _ _ h]

def subst_all_var (args: List Term) (hargs: ∀arg ∈ args, arg.IsClosed 0) (index: Nat) (h: index < args.length) :
  subst_all 0 args (.var index) = args[index] := by
  induction args generalizing index with
  | nil => contradiction
  | cons arg args ih =>
    cases index
    simp [subst_var_eq]
    rw [susbt_all_closed]
    apply hargs
    simp
    simp
    apply ih
    intro arg h
    apply hargs
    simp [h]

def subst_all_lam (args: List Term) (hargs: ∀arg ∈ args, arg.IsClosed 0) (body: Term) :
  subst_all n args body.lam = (subst_all (n + 1) args body).lam := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    simp; rw [ih]
    congr
    rw [weaken_closed]
    apply hargs
    simp
    intro _ h
    apply hargs
    simp [h]

def subst_all_app (args: List Term) (func arg: Term) :
  subst_all n args (func.app arg)  = (subst_all n args func).app (subst_all n args arg) := by
  induction args generalizing func arg with
  | nil => rfl
  | cons arg args ih => simp [ih]

end Term

end TypeTheory
