import LeanMath.Tactic.TypeStar
import LeanMath.Tactic.AxiomBlame

namespace Nat

structure GcdAux where
  a: ℤ
  b: ℤ
deriving Repr

private def xgcdAux.fueled_rec_lemma (r r': ℕ) (fuel: ℕ) (hfuel: r' < fuel + 1) (h: r' ≠ 0) :
  r % r' < fuel := by
  apply Nat.lt_of_lt_of_le
  apply Nat.mod_lt
  apply Nat.pos_of_ne_zero
  assumption
  apply Nat.le_of_lt_succ
  assumption

private def xgcdAux.fueled (r r': ℕ) (s s' t t': ℤ) (fuel: ℕ) (hfuel: r' < fuel) : ℤ × ℤ × ℕ :=
  match fuel with
  | fuel + 1 =>
  if hr':r' = 0 then
    ⟨s, t ,r⟩
  else
    let q := r / r'
    xgcdAux.fueled
      r' (r - q * r')
      s' (s - q * s')
      t' (t - q * t')
      fuel <| by
      rw [←Nat.mod_eq_sub_div_mul]
      apply xgcdAux.fueled_rec_lemma
      assumption
      assumption

private def xgcdAux.fueled_irrel (r r': ℕ) (s s' t t': ℤ) (fuel₀ fuel₁: ℕ) (hfuel₀: r' < fuel₀) (hfuel₁: r' < fuel₁) :
  fueled r r' s s' t t' fuel₀ hfuel₀ = fueled r r' s s' t t' fuel₁ hfuel₁ := by
  induction fuel₀ using Nat.strongRecOn generalizing r r' s s' t t' fuel₁ with | _ fuel₀ ih =>
  match fuel₀, fuel₁ with
  | fuel₀ + 1, fuel₁ + 1 =>
  unfold fueled
  split; rfl
  dsimp
  apply ih
  apply Nat.lt_succ_self

private def xgcdAux (r r': ℕ) (s s' t t': ℤ) : ℤ × ℤ × ℕ :=
  xgcdAux.fueled r r' s s' t t' (r' + 1) (Nat.lt_succ_self _)

private def xgcdAux.fueled_eq (r r': ℕ) (s s' t t': ℤ) (fuel: ℕ) (hfuel: r' < fuel) :
  fueled r r' s s' t t' fuel hfuel = xgcdAux r r' s s' t t' := by
  apply xgcdAux.fueled_irrel

private def xgcdAux_zero : xgcdAux r 0 s s' t t' = ⟨s, t, r⟩ := rfl
private def xgcdAux_ne_zero (h: r' ≠ 0) : xgcdAux r r' s s' t t' =
  xgcdAux
      r' (r - r / r' * r')
      s' (s - r / r' * s')
      t' (t - r / r' * t') := by
  conv => {
    lhs; unfold xgcdAux xgcdAux.fueled
    rw [dif_neg h]
  }
  rw [xgcdAux.fueled_eq]
  rfl

def xgcd (a b: ℕ) : ℤ × ℤ × ℕ :=
  xgcdAux b a 0 1 1 0

def gcdA (a b: ℕ) : ℤ := (xgcd a b).1
def gcdB (a b: ℕ) : ℤ := (xgcd a b).2.1
def gcd' (a b: ℕ) : ℕ := (xgcd a b).2.2

@[simp] def gcdA_zero_left : gcdA 0 b = 0 := by
  simp [gcdA, xgcd, xgcdAux_zero]
@[simp] def gcdB_zero_left : gcdB 0 b = 1 := by
  simp [gcdB, xgcd, xgcdAux_zero]
@[simp] def gcdA_zero_right (h: a ≠ 0) : gcdA a 0 = 1 := by
  simp [gcdA, xgcd, xgcdAux_ne_zero, h]; rfl
@[simp] def gcdB_zero_right (h: a ≠ 0) : gcdB a 0 = 0 := by
  simp [gcdB, xgcd, xgcdAux_ne_zero, h]; rfl

def GcdP (a b: ℕ) : ℤ × ℤ × ℕ -> Prop :=
  fun (s, t, r) => r = a * s + b * t

def GcdP_spec : GcdP a b ⟨s, t, r⟩ -> GcdP a b ⟨s', t', r'⟩ -> GcdP a b (xgcdAux r r' s s' t t') := by
  intro h₀ h₁
  induction r', r using Nat.gcd.induction generalizing s s' t t' with
  | H0 =>
    rw [xgcdAux_zero]
    assumption
  | H1 r' r r'_ne_zero ih =>
    rw [xgcdAux_ne_zero]
    rw [←Nat.mod_eq_sub_div_mul]
    apply ih
    assumption
    show _ = _
    rw [Nat.mod_eq_sub_div_mul]
    replace h₀: _ = _ := h₀
    replace h₁: _ = _ := h₁
    · rw [Int.mul_comm (r / r'), Int.mul_comm (r / r')]
      rw [Int.mul_sub, Int.mul_sub,
        Int.sub_eq_add_neg, Int.sub_eq_add_neg,
        Int.add_assoc, Int.add_left_comm _ (b * t),
        ←Int.add_assoc, ←Int.neg_add, ←Int.mul_assoc, ←Int.mul_assoc,
        ←Int.add_mul, ←h₁, ←h₀, ←Int.sub_eq_add_neg, Int.mul_comm,
        ←Nat.mod_eq_sub_div_mul]
      symm; rw [Int.sub_eq_iff_eq_add, Int.natCast_emod,
        Int.emod_add_ediv_mul]
    · apply Nat.ne_of_gt
      assumption

def gcd_eq_gcdAux (a b: ℕ) :
  gcd a b = (xgcdAux b a s s' t t').2.2 := by
  induction a, b using Nat.gcd.induction generalizing s s' t t' with
  | H0 n => rw [xgcdAux_zero, Nat.gcd_zero_left]
  | H1 n m npos ih =>
    rw [xgcdAux_ne_zero]
    rw [←Nat.mod_eq_sub_div_mul]
    unfold gcd
    rw [if_neg]
    rw [ih]
    iterate 2
    apply Nat.ne_of_gt
    assumption

def bezout (a b: ℕ) : gcd a b = a * gcdA a b + b * gcdB a b := by
  rw [gcd_eq_gcdAux]
  show ((xgcd a b).snd.snd: ℤ) = _
  apply GcdP_spec
  simp [GcdP]
  simp [GcdP]

end Nat
