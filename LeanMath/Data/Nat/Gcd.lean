import LeanMath.Tactic.TypeStar

namespace Nat

structure GcdAux where
  a: ℤ
  b: ℤ
deriving Repr

private def xgcdAux (r r': ℕ) (s s' t t': ℤ) : ℤ × ℤ × ℕ :=
  if r' = 0 then
    ⟨s, t ,r⟩
  else
    let q := r / r'
    xgcdAux
      r' (r - q * r')
      s' (s - q * s')
      t' (t - q * t')
termination_by r'
decreasing_by
  rw [←Nat.mod_eq_sub_div_mul]
  apply Nat.mod_lt
  omega

def xgcd (a b: ℕ) : ℤ × ℤ × ℕ :=
  xgcdAux b a 0 1 1 0

def gcdA (a b: ℕ) : ℤ := (xgcd a b).1
def gcdB (a b: ℕ) : ℤ := (xgcd a b).2.1
def gcd' (a b: ℕ) : ℕ := (xgcd a b).2.2

@[simp] def gcdA_zero_left : gcdA 0 b = 0 := by
  simp [gcdA, xgcd, xgcdAux]
@[simp] def gcdB_zero_left : gcdB 0 b = 1 := by
  simp [gcdB, xgcd, xgcdAux]
@[simp] def gcdA_zero_right (h: a ≠ 0) : gcdA a 0 = 1 := by
  simp [gcdA, xgcd, xgcdAux, h]
@[simp] def gcdB_zero_right (h: a ≠ 0) : gcdB a 0 = 0 := by
  simp [gcdB, xgcd, xgcdAux, h]

def GcdP (a b: ℕ) : ℤ × ℤ × ℕ -> Prop :=
  fun (s, t, r) => r = a * s + b * t

def GcdP_spec : GcdP a b ⟨s, t, r⟩ -> GcdP a b ⟨s', t', r'⟩ -> GcdP a b (xgcdAux r r' s s' t t') := by
  intro h₀ h₁
  induction r, r', s, s', t, t' using xgcdAux.induct with
  | case1 =>
    unfold xgcdAux
    rw [if_pos rfl]
    assumption
  | case2 r r' s s' t t' hr' q ih =>
    unfold xgcdAux
    rw [if_neg hr']
    dsimp
    apply ih
    assumption
    show _ = _
    rw [←Nat.mod_eq_sub_div_mul]
    replace h₀: _ = _ := h₀
    replace h₁: _ = _ := h₁
    rw [Int.mul_sub, Int.mul_sub, Int.mul_comm q, Int.mul_comm q,
      ←Int.mul_assoc, ←Int.mul_assoc]
    rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg,
      ←Int.add_assoc, Int.add_assoc (a * s), Int.add_comm _ (b * t),
      ←Int.add_assoc, Int.add_assoc (_ + _), ←Int.neg_add,
      ←Int.add_mul, ←h₀, ←h₁,
      ←Int.sub_eq_add_neg]
    rw [←Int.emod_add_ediv_mul r r',
      Int.add_sub_assoc, Int.mul_comm]
    simp [q]

def gcd_eq_gcdAux (a b: ℕ) :
  gcd a b = (xgcdAux b a s s' t t').2.2 := by
  induction a, b using Nat.gcd.induction generalizing s s' t t' with
  | H0 n => simp [xgcdAux]
  | H1 n m npos ih =>
    unfold xgcdAux
    rw [if_neg]
    dsimp
    rw [←Nat.mod_eq_sub_div_mul]
    unfold gcd
    rw [if_neg]
    rw [ih]
    omega
    omega

def bezout (a b: ℕ) : gcd a b = a * gcdA a b + b * gcdB a b := by
  rw [gcd_eq_gcdAux]
  show ((xgcd a b).snd.snd: ℤ) = _
  apply GcdP_spec
  simp [GcdP]
  simp [GcdP]

end Nat
