import LeanMath.Data.Fintype.Choice
import LeanMath.Data.Fintype.Algebra.Monoid
import LeanMath.Data.Nat.Basic

namespace Pi

private def pi (n: ℕ) (card: Fin n -> ℕ) :
  Fin (∏i, card i) ↭ (∀i, Fin (card i)) :=
  match n with
  | 0 => {
    toFun := nofun
    inj' := by
      intro a b h
      dsimp at h
      apply Subsingleton.allEq (α := Fin 1)
    surj' := by
      intro f
      exists ⟨0, Nat.zero_lt_succ _⟩
      ext x; exact x.elim0
  }
  | n + 1 =>
    let card0 := card 0
    have cardsucc := pi n (card ∘ Fin.succ)
    have eqv := (Fin.prod (card 0) (∏i: Fin n, card i.succ)).comp
      (Equiv.fin_cast (n := ∏i, card i) (m := card 0 * ∏i: Fin n, card i.succ) (by rw [fin_prod_succ]))
    eqv.toBij.trans {
      toFun
      | idx, ⟨0, _⟩ => idx.fst
      | idx, ⟨i + 1, hi⟩ => cardsucc idx.snd ⟨i, Nat.lt_of_succ_lt_succ hi⟩
      inj' := by
        intro i j h
        dsimp at h
        replace h := congrFun h
        ext1; exact h ⟨0, Nat.zero_lt_succ _⟩
        apply cardsucc.inj
        funext x; apply h x.succ
      surj' f := by
        have ⟨b, hb⟩ := cardsucc.surj (fun i: Fin n => f i.succ)
        refine ⟨⟨?_, ?_⟩, ?_⟩
        exact f 0
        exact b
        ext1 i; cases i using Fin.cases
        rfl
        simp [Fin.succ]
        apply congrFun hb
    }

private def func' {n m: ℕ} (idx i: ℕ) (hidx: idx < m ^ n) (hi: i < n) : Fin m where
  val := idx / (m ^ i) % m
  isLt := by
    apply Nat.mod_lt
    apply Nat.pos_of_ne_zero
    rintro rfl
    rw [Nat.zero_pow] at hidx
    contradiction
    apply Nat.pos_of_ne_zero
    rintro rfl
    contradiction

private def add_mul_lt_mul (a b c d: ℕ) :
  a < c -> b < d ->
  a + c * b < c * d := by
  intro ac bd
  cases d with
  | zero => contradiction
  | succ d =>
  rw [Nat.mul_succ _, add_comm _ c]
  apply Nat.add_lt_add_of_lt_of_le
  assumption
  apply Nat.mul_le_mul
  apply Nat.le_refl
  apply Nat.le_of_lt_succ
  assumption

private def sum_lt (f: Fin n -> Fin m) : ∑ i, ↑(f i) * m ^ i.val < m ^ n := by
  induction n with
  | zero => apply Nat.zero_lt_succ
  | succ n ih =>
    rw [fin_sum_succ]
    dsimp
    rw  [npow_succ, mul_one, mul_comm]
    simp [npow_succ, mul_comm _ m, ←mul_assoc]
    simp [mul_assoc]
    conv => { lhs; simp [←smul_eq_mul m] }
    rw [smul_sum, smul_eq_mul]
    apply add_mul_lt_mul
    apply Fin.isLt
    apply ih

private def func'_spec {n m: ℕ} (idx: ℕ) (hidx: idx < m ^ n) : ∑i: Fin n, func' idx i.val hidx i.isLt * m ^ i.val = idx := by
  simp [func']
  induction n generalizing idx with
  | zero => match idx with | 0 => rfl
  | succ n ih =>
    rw (occs := [2]) [←Nat.mod_add_div idx m]
    rw [fin_sum_succ]; simp
    simp [npow_succ, mul_comm _ m, ←Nat.div_div_eq_div_mul,
    ←mul_assoc]
    simp [mul_assoc]
    conv => { lhs; simp [←smul_eq_mul m] }
    rw [smul_sum, smul_eq_mul]
    congr 1
    apply ih
    rw [npow_succ, mul_comm] at hidx
    apply Nat.div_lt_of_lt_mul'
    assumption

private def func (n m: ℕ) : Fin (m ^ n) ↭ (Fin n -> Fin m) where
  toFun idx i := func' idx i idx.isLt i.isLt
  inj' := by
    intro a b hi
    replace hi : ∀x, _ := congrFun hi
    simp at hi
    ext; rw [←func'_spec (n := n) (m := m) a, ←func'_spec (n := n) (m := m) b]
    congr; ext1 i; congr 2; apply hi i
    exact b.isLt
    exact a.isLt
  surj' := by
    intro f
    dsimp
    exists {
      val := ∑i: Fin n, f i * m ^ i.val
      isLt := sum_lt _
    }
    ext i; dsimp [func']
    induction n with
    | zero => exact i.elim0
    | succ n ih =>
      cases i using Fin.cases with
      | zero =>
        simp
        simp [npow_succ, mul_comm _ m, ←mul_assoc]
        simp [mul_assoc]
        simp [←smul_eq_mul m]
        rw [smul_sum, smul_eq_mul, Nat.add_mod, Nat.mul_mod_right,
          Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt]
        apply Fin.isLt
      | succ n =>
        simp [npow_succ, mul_comm _ m, ←mul_assoc]
        simp [mul_assoc]
        simp [←smul_eq_mul m]
        rw [smul_sum]
        simp [smul_eq_mul]
        rw [
          ←Nat.div_div_eq_div_mul, Nat.add_mul_div_left,
          Nat.div_eq_of_lt _ (b := m), zero_add]
        apply ih
        apply Fin.isLt
        exact (f n.succ).pos

private def card_all_eq' (card: ℕ) : ∀(n: ℕ), (∀x < n, ℕ) -> Bool
| 0, _ => true
| n + 1, f =>
  if f n (Nat.lt_succ_self _) = card then
    card_all_eq' card n (fun x h => f x (Nat.lt_trans h (Nat.lt_succ_self _)))
  else
    false

private def card_all_eq'_spec (card: ℕ) {n: ℕ} (f: ∀x < n, ℕ) :
  card_all_eq' card n f ↔ ∀i hi, f i hi = card := by
  induction n with
  | zero => simp; rfl
  | succ n ih =>
    unfold card_all_eq'
    simp; apply Iff.intro
    · intro ⟨h₀, h₁⟩ i hi
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hi
      rcases hi with hi | rfl
      exact (ih (fun x h => f x _)).mp h₁ i hi
      assumption
    · intro h
      apply And.intro
      exact h n _
      apply (ih _).mpr
      intro i hi
      apply h

private def card_all_eq : ∀(n: ℕ) (f: ∀x < n, ℕ), Option (Σ'card: ℕ, ∀i hi, f i hi = card)
| 0, _ => .some ⟨0, nofun⟩
| n + 1, f =>
  let c := (f n (Nat.lt_succ_self _))
  if h:card_all_eq' (f n (Nat.lt_succ_self _)) n (fun x h => f x (Nat.lt_trans h (Nat.lt_succ_self _))) then
    .some ⟨c, by
      intro i hi
      rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hi
      rcases hi with hi | rfl
      exact (card_all_eq'_spec _ _).mp h _ hi
      rfl⟩
  else
    .none

private def instPiFin (card: Fin n -> ℕ) : Fintype (∀i: Fin n, Fin (card i)) where
  card := ∏i, card i
  repr := Trunc.mk {
    try_decode := .none
    bij := pi _ _
  }
private def instFuncFin : Fintype (Fin n -> Fin m) where
  card := m ^ n
  repr := Trunc.mk {
    try_decode := .none
    bij := func _ _
  }

end Pi

namespace Fintype

section

variable {ι: Sort*} {α: ι -> Sort*} [fι: Fintype ι] [DecidableEq ι] [fα: ∀i, Fintype (α i)]

instance (priority := 100) : Fintype (∀i, α i) :=
  (Fintype.finEquiv ι).recOnSubsingleton fun rι =>
  (finTruncChoice (fun i => Fintype.finBij (α i))).recOnSubsingleton fun rα =>
  match Pi.card_all_eq (Fintype.card ι) (fun i hi => Fintype.card (α (rι ⟨i, hi⟩))) with
  | .some ⟨card, hcard⟩ => by
    replace rα (i: ι) : Fin card ↭ α i :=
      (Equiv.fin_cast ?_).toBij.trans (rα i)
    · -- this is a function type, where all targets have the same cardinality
      have := @Pi.instFuncFin
      apply Fintype.ofBij (α := Fin (Fintype.card ι) -> Fin card)
      exact {
        toFun f i := rα i (f (rι.symm i))
        inj' := by
          intro f₀ f₁ h
          replace h := congrFun h; dsimp at h
          ext1 i
          have := h (rι i)
          simp at this
          exact (rα _).inj this
        surj' := by
          intro f
          have (i: ι) : ∃x: Fin card, (rα i) x = f i := by
            apply (rα _).surj
          replace := finChoice this
          obtain ⟨g, hg⟩ := this
          refine ⟨fun i => g (rι i), ?_⟩
          ext i; simp; apply hg
      }
    · rw [←hcard (rι.symm i) (Fin.isLt _)]
      congr <;> (show rι (rι.symm _) = _; simp)
  | .none => by
    have := @Pi.instPiFin
    apply Fintype.ofBij (α := ∀i: Fin (Fintype.card ι), Fin (Fintype.card (α (rι i))))
    exact {
      toFun f i := rα i <| (f (rι.symm i)).cast <| by
        congr <;> rw [Equiv.symm_coe]
      inj' := by
        intro f₀ f₁ h
        replace h := congrFun h; dsimp at h
        ext1 i
        have := h (rι i)
        simp at this
        replace := (rα _).inj this
        rw [←Fin.val_inj] at this
        dsimp at this
        rwa [Fin.val_inj, rι.coe_symm] at this
      surj' := by
        intro f
        have (i: ι) : ∃x: Fin (Fintype.card (α i)), (rα i) x = f i := by
          apply (rα _).surj
        replace := finChoice this
        obtain ⟨g, hg⟩ := this
        refine ⟨fun i => g (rι i), ?_⟩
        ext i; simp
        rw [show Fin.cast _ (g (rι (rι.symm i))) = g i from ?_]
        rw [hg]
        rw [←Fin.val_inj]; simp
        rw [Equiv.symm_coe]
    }

end

section

variable {ι α: Sort*} [fι: Fintype ι] [DecidableEq ι] [fα: Fintype α]

instance (priority := 10000) instFunc : Fintype (ι -> α) :=
  (Fintype.finEquiv ι).recOnSubsingleton fun rι =>
  (Fintype.finBij α).recOnSubsingleton fun rα => by
  have := @Pi.instFuncFin
  let card := Fintype.card α
  apply Fintype.ofBij (α := Fin (Fintype.card ι) -> Fin card)
  exact {
    toFun f i := rα (f (rι.symm i))
    inj' := by
      intro f₀ f₁ h
      replace h := congrFun h; dsimp at h
      ext1 i
      have := h (rι i)
      simp at this
      exact rα.inj this
    surj' := by
      intro f
      have (i: ι) : ∃x: Fin card, rα x = f i := by
        apply rα.surj
      replace := finChoice this
      obtain ⟨g, hg⟩ := this
      refine ⟨fun i => g (rι i), ?_⟩
      ext i; simp; apply hg
  }

end

end Fintype

namespace Finite

variable
  {α: ι -> Sort*}
  [fι: Finite ι] [DecidableEq ι] [fα: ∀i, Finite (α i)]

instance : Finite (∀i, α i) := by
  have ⟨fα⟩ := finChoose fα
  obtain ⟨fι⟩ := fι
  have : DecidableEq ι := inferInstance
  exact ⟨inferInstance⟩

end Finite
