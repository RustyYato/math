import LeanMath.Data.Equiv.Defs
import LeanMath.Data.Nat.Div
import LeanMath.Tactic.AxiomBlame

private def nat_add_sub_cancel (a b: Nat) : a + b - b = a := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.add_succ, Nat.succ_sub_succ, ih]

private def nat_exists_eq_add_of_le {a b: Nat} : a ≤ b -> ∃k, b = a + k := by
  intro h
  induction b with
  | zero =>
    cases Nat.le_zero.mp h; exists 0
  | succ b ih =>
    replace h := Nat.lt_or_eq_of_le h
    rcases h with h | h
    · have ⟨k, h⟩ := ih (Nat.le_of_lt_succ h)
      exists k + 1
      rw [←Nat.add_assoc, h]
    · subst a
      exists 0

private def nat_lt_add_of_sub_lt (a b c: Nat) : a - b < c -> a < b + c := by
  induction b generalizing a c with
  | zero =>
    rw [Nat.zero_add, Nat.sub_zero]
    exact id
  | succ b ih =>
    cases a with
    | zero =>
      intro;
      rw [Nat.succ_add]
      apply Nat.zero_lt_succ
    | succ a =>
      rw [Nat.succ_sub_succ, Nat.succ_add]
      intro h
      apply Nat.succ_lt_succ
      apply ih
      assumption

private def nat_sub_lt_of_lt_add (a b c: Nat) (h: b ≤ a) : a < b + c -> a - b < c := by
  induction b generalizing a c with
  | zero =>
    rw [Nat.zero_add, Nat.sub_zero]
    exact id
  | succ b ih =>
    cases a with
    | zero =>
      intro
      nomatch h
    | succ a =>
      rw [Nat.succ_sub_succ, Nat.succ_add]
      intro h
      apply ih
      apply Nat.le_of_succ_le_succ
      assumption
      apply Nat.lt_of_succ_lt_succ
      assumption

private def nat_div_lt_of_lt_mul {m n k : Nat} (h : m < n * k) : m / n < k := by
  induction m, n using Nat.div.inductionOn generalizing k with
  | base n m g =>
    rw [nat_div_eq, if_neg g]
    cases k
    rw [Nat.mul_zero] at h
    contradiction
    apply Nat.zero_lt_succ
  | ind n m g ih =>
    rw [nat_div_eq, if_pos g]
    cases k with
    | zero =>
      rw [Nat.mul_zero] at h
      contradiction
    | succ k =>
      rw [Nat.mul_succ] at h
      rw [Nat.add_comm] at h
      apply Nat.succ_lt_succ
      refine ih (nat_sub_lt_of_lt_add _ _ _ ?_ h)
      exact g.right

private def nat_mod_eq_of_lt (n m: Nat) (h: n < m) : n % m = n := by
  rw [nat_mod_eq, if_neg]
  intro ⟨_, g⟩
  exact Nat.not_lt_of_le g h

private def nat_mod_mod (n m: Nat) : n % m % m = n % m := by
  refine if h:m = 0 then ?_ else ?_
  subst m; rw [nat_mod_eq, if_neg]
  intro ⟨_, _⟩
  contradiction
  rw [nat_mod_eq_of_lt]
  apply mod_lt
  apply Nat.pos_of_ne_zero
  assumption

private def nat_div_eq_of_lt (n m: Nat) (h: n < m) : n / m = 0 := by
  rw [nat_div_eq, if_neg]
  intro ⟨_, g⟩
  exact Nat.not_lt_of_le g h

private def nat_mod_zero (n: Nat) : n % 0 = n := by
  rw [nat_mod_eq, if_neg]
  intro h
  nomatch h

private def nat_add_mod_right (x z : Nat) : (x + z) % z = x % z := by
  refine if h:z = 0 then ?_ else ?_
  subst z
  rw [nat_mod_zero, nat_mod_zero, Nat.add_zero]
  rw [nat_mod_eq, if_pos, nat_add_sub_cancel]
  apply And.intro
  apply Nat.pos_of_ne_zero
  assumption
  apply Nat.le_add_left

private def nat_add_mul_mod_self_left (x y z : Nat) : (x + y * z) % y = x % y := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ z ih =>
    rw [Nat.mul_succ, ←Nat.add_assoc, nat_add_mod_right, ih]

private theorem nat_add_mul_div_right (x y : Nat) {z : Nat} (H : 0 < z) : (x + y * z) / z = x / z + y := by
  induction y with
  | zero => rw [Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  | succ y ih =>
    rw [Nat.succ_mul, ←Nat.add_assoc, nat_div_eq, if_pos, nat_add_sub_cancel, ih, Nat.add_assoc]
    apply And.intro H
    apply Nat.le_add_left

namespace Fin

def sum (n m: Nat) : Fin (n + m) ≃ Fin n ⊕ Fin m where
  toFun x :=
    if h:x.val < n then
      .inl ⟨_, h⟩
    else
      .inr ⟨x.val - n, by
        replace h := Nat.le_of_not_lt h
        apply nat_sub_lt_of_lt_add
        assumption
        exact x.isLt⟩
  invFun
  | .inl x => ⟨x.val, Nat.lt_of_lt_of_le x.isLt (Nat.le_add_right _ _)⟩
  | .inr x => ⟨n + x.val, Nat.add_lt_add_left x.isLt _⟩
  leftInv x := by
    rcases x with x | x
    · dsimp
      rw [dif_pos x.isLt]
    · dsimp
      rw [dif_neg]
      congr
      rw [Nat.add_comm, nat_add_sub_cancel]
      apply Nat.not_lt_of_le
      apply Nat.le_add_right
  rightInv x := by
    dsimp
    by_cases h:x.val < n
    rw [dif_pos h]
    rw [dif_neg h]
    dsimp; congr
    rw [Nat.add_comm]
    obtain ⟨i, h⟩ := nat_exists_eq_add_of_le (Nat.le_of_not_lt h)
    rw [h, Nat.add_comm n, nat_add_sub_cancel]

def prod (n m: Nat) : Fin (n * m) ≃ Fin n × Fin m where
  toFun x := {
    fst := {
      val := x % n
      isLt := by
        apply mod_lt
        have := x.pos
        cases n
        rw [Nat.zero_mul] at this
        assumption
        apply Nat.zero_lt_succ
    }
    snd := {
      val := x / n
      isLt := by
        apply nat_div_lt_of_lt_mul
        exact x.isLt
    }
  }
  invFun x := {
    val := x.fst.val + x.snd.val * n
    isLt := by
      cases m with
      | zero => exact x.snd.elim0
      | succ m =>
        rw [Nat.mul_succ, Nat.add_comm]
        apply Nat.add_lt_add_of_le_of_lt
        rw [Nat.mul_comm]
        apply Nat.mul_le_mul_left
        apply Nat.le_of_lt_succ
        exact x.snd.isLt
        exact x.fst.isLt
  }
  leftInv := by
    intro ⟨a, b⟩
    dsimp; congr
    · rw [Nat.mul_comm, nat_add_mul_mod_self_left, nat_mod_eq_of_lt]
      exact a.isLt
    · rw [nat_add_mul_div_right, nat_div_eq, if_neg, Nat.zero_add]
      intro ⟨_, h⟩
      exact Nat.not_lt_of_le h a.isLt
      exact a.pos
  rightInv := by
    intro x
    dsimp
    congr
    rw [Nat.add_comm, Nat.mul_comm, nat_div_add_mod]

end Fin
