import LeanMath.Data.Fintype.Defs
import LeanMath.Data.Fintype.Pairing
import LeanMath.Algebra.Monoid.Action.Defs

def sum [Fintype ι] [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  (f: ι -> α) : α :=
  Fintype.fold (fun i a => f i + a) (by
    intro i j a
    dsimp; ac_rfl) 0

def prod  [Fintype ι] [MonoidOps α] [IsMonoid α] [IsComm α]
  (f: ι -> α) : α := AddOfMul.get (sum (AddOfMul.mk ∘ f))

section Syntax

open Lean
open TSyntax.Compat

macro "∑ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``sum xs b
macro "∏ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``prod xs b

@[app_unexpander sum] def unexpand_sum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∑ $xs:binderIdent*, $b) => `(∑ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∑ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∑ ($x:ident : $t), $b)
  | _                                              => throw ()

@[app_unexpander prod] def unexpand_prod : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ∏ $xs:binderIdent*, $b) => `(∏ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(∏ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(∏ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax

variable
  {ι ι': Sort*}
  {α β F: Type*}
  [Fintype ι] [Fintype ι']
  [FunLike F α β]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  [MonoidOps α] [IsMonoid α] [IsComm α]
  [AddMonoidOps β] [IsAddMonoid β] [IsAddComm β]
  [MonoidOps β] [IsMonoid β] [IsComm β]
  [IsZeroHom F α β] [IsAddHom F α β]
  [IsOneHom F α β] [IsMulHom F α β]

@[simp] def fin_sum_zero (f: Fin 0 -> α) : ∑i, f i = 0 := rfl
@[simp] def fin_sum_succ (f: Fin (n + 1) -> α) : ∑i, f i = f 0 + ∑i: Fin n, f i.succ := by
  rw [sum, Fintype.fold_succ]
  rfl

@[simp] def fin_prod_zero (f: Fin 0 -> α) : ∏i, f i = 1 := rfl
@[simp] def fin_prod_succ (f: Fin (n + 1) -> α) : ∏i, f i = f 0 * ∏i: Fin n, f i.succ :=
  fin_sum_succ (α := AddOfMul α) _

def sum_reindex (bij: ι ↭ ι') (f: ι' -> α) : ∑i, f i = ∑i, f (bij i) := by
  apply Fintype.fold_bij

def prod_reindex (bij: ι ↭ ι') (f: ι' -> α) : ∏i, f i = ∏i, f (bij i) :=
  sum_reindex (α := AddOfMul α) _ _

@[simp] def sum_empty [IsEmpty ι] (f: ι -> α) : ∑i, f i = 0 := by
  rename Fintype ι => ft
  rw [show ft = Fintype.instOfIsEmpty from Subsingleton.allEq _ _]
  rfl

@[simp] def prod_empty [IsEmpty ι] (f: ι -> α) : ∏i, f i = 1 :=
  sum_empty (α := AddOfMul α) _

@[simp] def sum_poption (f: POption ι -> α) : (∑i, f i) = f .none + ∑i, f (.some i) := by
  induction Fintype.finBij ι with | mk bij =>
  rw [sum_reindex (Bijection.finsucc_poption bij), sum_reindex bij]
  simp; rfl

@[simp] def prod_poption (f: POption ι -> α) : (∏i, f i) = f .none * ∏i, f (.some i) :=
  sum_poption (α := AddOfMul α) _

private def map_sum' (f: Fin n -> α) (g: F) : sum (g ∘ f) = g (sum f) := by
  induction n with
  | zero => simp [map_zero]
  | succ n ih =>
    simp [map_add, ←ih]
    rfl

def map_sum (f: ι -> α) (g: F) : (∑i, g (f i)) = g (∑i, f i) := by
  induction Fintype.finBij ι with | mk bij =>
  rw [sum_reindex bij, sum_reindex bij]
  apply map_sum'

def map_prod (f: ι -> α) (g: F) : (∏i, g (f i)) = g (∏i, f i) :=
  map_sum
    (α := AddOfMul α) (β := AddOfMul β)
    (F := AddOfMul α →+ AddOfMul β)
    (f := fun i => AddOfMul.mk (f i))
    (g := {
    toFun := _
    map_zero := map_one g
    map_add := map_mul g
  })

private def sum_psum' (f: (Fin n ⊕' Fin m) -> α) : (∑i, f i) = (∑i, f (.inl i)) + (∑i, f (.inr i)) := by
  induction n generalizing m with
  | zero =>
    simp [zero_add]
    let bij : Fin m ↭ (Fin 0 ⊕' Fin m) := {
      toFun := .inr
      inj' _ _ := PSum.inr.inj
      surj' := ?_
    }
    apply sum_reindex bij
    intro x; rcases x with x | x
    exact x.elim0
    exists x
  | succ n ih =>
    let bij : (POption (Fin n ⊕' Fin m)) ↭ (Fin (n + 1) ⊕' Fin m) := {
      toFun
      | .none => .inl 0
      | .some (.inl x) => .inl x.succ
      | .some (.inr x) => .inr x
      inj' := ?_
      surj' := ?_
    }
    rw [sum_reindex bij]
    simp [ih, add_assoc]; rfl
    · intro a b h
      rcases a with _ | a | a <;> rcases b with _ | b | b
      all_goals dsimp at h
      any_goals contradiction
      · rfl
      · nomatch h
      · nomatch h
      · rw [Fin.succ_inj.mp (PSum.inl.inj h)]
      · rw [PSum.inr.inj h]
    · intro x
      rcases x with x | x
      cases x using Fin.cases
      exists .none; rename_i x
      exists .some (.inl x)
      exists .some (.inr x)

def sum_psum (f: (ι ⊕' ι') -> α) : (∑i, f i) = (∑i, f (.inl i)) + (∑i, f (.inr i)) := by
  induction Fintype.finBij ι with | mk ιbij =>
  induction Fintype.finBij ι' with | mk ι'bij =>
  rw [sum_reindex ιbij, sum_reindex ι'bij]
  rw [sum_reindex (Bijection.psum_congr ιbij ι'bij)]
  apply sum_psum'

private def sum_sum' (f: Fin n -> Fin m -> α) : ∑i j, f i j = ∑i: Fin n × Fin m, f i.1 i.2 := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    simp
    let bij : (Fin m ⊕' Fin n × Fin m) ↭ (Fin (n + 1) × Fin m) := {
      toFun
      | .inl x => ⟨0, x⟩
      | .inr x => ⟨x.1.succ, x.2⟩
      inj' := ?_
      surj' := ?_
    }
    · rw [sum_reindex bij, sum_psum]
      simp [show ∀i, bij (.inl i) = ⟨0, i⟩ from fun _ => rfl]
      congr 1
      apply ih
    · intro x y h
      rcases x with x | x <;> rcases y with y | y
      rw [(Prod.mk.inj h).right]
      nomatch Fin.succ_ne_zero _ (Prod.mk.inj h).left.symm
      nomatch Fin.succ_ne_zero _ (Prod.mk.inj h).left
      have := (Prod.mk.inj h)
      rw [Fin.succ_inj] at this
      congr; apply Prod.ext
      exact this.left
      exact this.right
    · intro x
      obtain ⟨x, y⟩ := x
      cases x using Fin.cases
      exists .inl y
      rename_i x
      exists .inr ⟨x, y⟩

def sum_sum (f: ι -> ι' -> α) : ∑i j, f i j = ∑i: ι ×' ι', f i.1 i.2 := by
  induction Fintype.finBij ι with | mk ιbij =>
  induction Fintype.finBij ι' with | mk ι'bij =>
  simp [sum_reindex ιbij, sum_reindex ι'bij]
  rw [sum_reindex (Bijection.pprod_congr ιbij ι'bij)]
  show sum (fun i => sum fun j => f _ _) = sum fun i => f _ _
  rw [sum_sum']
  rfl

def prod_prod (f: ι -> ι' -> α) : ∏i j, f i j = ∏i: ι ×' ι', f i.1 i.2 :=
  sum_sum (α := AddOfMul α) _

private def sum_const' (x: α) : ∑_: Fin n, x = n • x := by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n ih => simp [succ_nsmul]; rw [add_comm]; congr

def sum_const (x: α) : ∑_: ι, x = Fintype.card ι • x := by
  induction Fintype.finBij ι with | _ bij =>
  rw [sum_reindex bij]
  apply sum_const'

def prod_const (x: α) : ∏_: ι, x = x ^ (Fintype.card ι) :=
  sum_const (α := AddOfMul α) _

def sum_zero : ∑_: ι, (0: α) = 0 := by
  rw [sum_const, nsmul_zero]

def prod_one : ∏_: ι, (1: α) = 1 :=
  sum_zero (α := AddOfMul α)

private def sum_pairwise' (f g: Fin n -> α) : (∑i, f i + g i) = (∑i, f i) + (∑i, g i) := by
  induction n with
  | zero => simp [add_zero]
  | succ n ih =>
    simp [ih]
    ac_rfl
def sum_pairwise (f g: ι -> α) : (∑i, f i + g i) = (∑i, f i) + (∑i, g i) := by
  induction Fintype.finBij ι with | mk f =>
  rw [sum_reindex f, sum_reindex f, sum_reindex f]
  apply sum_pairwise'

def prod_pairwise (f g: ι -> α) : (∏i, f i * g i) = (∏i, f i) * (∏i, g i) :=
  sum_pairwise (α := AddOfMul α) _ _

def sum_comm (f: ι -> ι' -> α) : ∑i j, f i j = ∑j i, f i j := by
  rw [sum_sum, sum_sum]
  apply sum_reindex Equiv.pprod_comm.toBij

def fin_sum_min (f: Fin n -> α) (m: ℕ) (hm: m ≤ n)
  : ∑i, f i = (∑i: Fin m, f (i.castLE hm)) + ∑i: Fin (n - m), f ((i.addNat m).cast (by rw [Nat.sub_add_cancel hm])) := by
  induction n generalizing m with
  | zero =>
    cases Nat.le_zero.mp hm
    symm; apply add_zero
  | succ n ih =>
    cases m with
    | zero =>
      rw [fin_sum_zero, zero_add]
      rfl
    | succ m =>
      rw [fin_sum_succ, fin_sum_succ, add_assoc]
      congr 1
      rw [ih (f := fun i => f i.succ) (m := m)]
      congr 1
      rw [sum_reindex (ι' := Fin ((n + 1) - (m + 1))) (ι := Fin (n - m)) (Equiv.fin_cast (by
        rw [Nat.succ_sub_succ])).toBij]
      dsimp
      congr
      apply Nat.le_of_succ_le_succ
      assumption

def fin_sum_min' (f: Fin n -> α) (m: ℕ) (hm: m ≤ n) (h: ∀i: Fin n, m ≤ i.val -> f i = 0)
  : ∑i, f i = (∑i: Fin m, f (i.castLE hm))  := by
  rw [fin_sum_min f m hm]
  conv => { lhs; rhs; arg 1; intro i; rw [h _ (by
    simp)] }
  rw [sum_zero, add_zero]

def fin_sum_succ_last (f: Fin (n + 1) -> α) : ∑i, f i = (∑i, f (Fin.castSucc i)) + f (Fin.last n) := by
  rw [sum_reindex Equiv.fin_rev.toBij, fin_sum_succ, sum_reindex Equiv.fin_rev.toBij, add_comm]
  congr 2; ext i; congr 1
  show Fin.rev (Fin.rev i).succ = _
  rw [Fin.rev_succ, Fin.rev_rev]

def sum_zero' (f: ι -> α) (hf: ∀i, f i = 0) : ∑i, f i = 0 := by
  simp [hf, sum_zero]

def smul_sum
  [SMul R α] [MonoidOps R] [IsMonoid R] [IsDistributiveAction R α]
  (r: R) (f: ι -> α) : ∑i, r • f i = r • ∑i, f i := by
  show ∑i, smulHom R (α := α) r (f i) = _
  rw [map_sum]
  rfl
