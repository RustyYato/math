import LeanMath.Algebra.Field.Defs
import LeanMath.Algebra.Dvd.Defs
import LeanMath.Tactic.AxiomBlame

@[ext]
structure Rational.Fract where
  num: ℤ
  den: ℕ
  den_ne_zero: den ≠ 0 := by decide
deriving Repr

def Rational.Fract.is_reduced (q: Fract) : Prop :=
  Int.gcd q.num q.den = 1

structure Rational extends Rational.Fract where
  ofFract ::
  reduced: toFract.is_reduced
deriving Repr

notation "ℚ" => Rational

namespace Rational

def Rel (a b: Fract) : Prop := a.num * b.den = b.num * a.den

instance : Relation.IsRefl Rational.Rel where
  refl _ := Eq.refl _
instance : Relation.IsSymm Rational.Rel where
  symm := Eq.symm
instance : Relation.IsTrans Rational.Rel where
  trans := by
    simp [Rational.Rel]
    intro a b c h g
    have : a.num * b.den * (b.num * c.den) = b.num * a.den * (c.num * b.den) := by rw [h, g]
    rw [
      show a.num * b.den * (b.num * c.den) = (a.num * c.den) * (b.num * b.den) by
        repeat rw [mul_assoc]
        congr 1; rw [←mul_assoc, mul_comm _ (c.den: ℤ), mul_comm _ b.num],
      show b.num * a.den * (c.num * b.den) = (c.num * a.den) * (b.num * b.den) by
        repeat rw [mul_assoc]
        repeat first|rw [mul_comm _ b.num]|rw [←mul_assoc _ b.num]
        repeat rw [←mul_assoc]
        congr 1; rw [mul_assoc c.num, mul_comm c.num,]] at this
    by_cases hb:b.num = 0
    rw [hb, zero_mul] at h g
    replace g := g.symm
    rcases of_mul_eq_zero h with h | h
    rcases of_mul_eq_zero g with g | g
    rw [h, g, zero_mul, zero_mul]
    nomatch b.den_ne_zero (Int.ofNat.inj g)
    nomatch b.den_ne_zero (Int.ofNat.inj h)
    refine of_mul_right₀ ?_ this
    intro h
    rcases of_mul_eq_zero h with h | h
    contradiction
    nomatch b.den_ne_zero (Int.ofNat.inj h)

instance setoid : Setoid Fract := (Relation.setoid Rational.Rel)

def Fract.den_pos (q: Fract) : 0 < q.den := Nat.pos_iff_ne_zero.mpr q.den_ne_zero

def toFract_inj : Function.Injective toFract := by
  intro a b h
  cases a; congr

def mk (q: Fract) : ℚ :=
  let g := q.num.gcd q.den
  {
    num := q.num / g
    den := q.den / g
    den_ne_zero := by
      apply Nat.ne_zero_iff_zero_lt.mpr
      apply Nat.div_pos
      apply Nat.le_of_dvd
      exact q.den_pos
      apply Nat.gcd_dvd_right
      apply Nat.ne_zero_iff_zero_lt.mp
      intro h
      have := (Nat.gcd_eq_zero_iff.mp h).right
      rw [Int.natAbs_natCast] at this
      exact q.den_ne_zero this
    reduced := by
      show _ = _
      simp
      apply of_mul_right₀ (k := g)
      intro h
      have := (Nat.gcd_eq_zero_iff.mp h).right
      rw [Int.natAbs_natCast] at this
      exact q.den_ne_zero this
      -- apply Int.natCast_inj.mp
      -- rw [natCast_mul, ]
      rw (occs := [3]) [←Int.natAbs_natCast g]
      rw [←Int.gcd_mul_right, Int.ediv_mul_cancel, Int.ediv_mul_cancel, one_mul]
      apply Int.gcd_dvd_right
      apply Int.gcd_dvd_left
  }

def mk_rel (q: Fract) : (mk q).toFract ≈ q := by
  show _ = _; dsimp [mk]
  rw [mul_comm _ (q.den: ℤ), ←Int.mul_ediv_assoc, ←Int.mul_ediv_assoc, mul_comm]
  apply Int.gcd_dvd_right
  apply Int.gcd_dvd_left

private def int_natCast_dvd_natCast {a b: ℕ} : (a: ℤ) ∣ (b: ℤ) ↔ a ∣ b := by
  apply Iff.intro
  · intro ⟨k, ha⟩
    cases k with
    | negSucc k =>
      rw [Int.ofNat_mul_negSucc] at ha
      match a with
      | a + 1 =>
        have := Int.natCast_nonneg b
        rw [ha] at this
        contradiction
      | 0 =>
        rw [zero_mul, natCast_zero, neg_zero] at ha
        cases Int.ofNat.inj ha
        apply Nat.dvd_refl
    | ofNat k =>
      rw [←natCast_mul] at ha
      cases Int.ofNat.inj ha
      apply Nat.dvd_mul_right
  · intro ⟨k, h⟩
    exists k
    rw [←natCast_mul]; congr

private def is_reduced_spec (a b: Fract) :
  a.is_reduced -> b.is_reduced ->
  a ≈ b -> a = b := by
  intro ha hb h
  have h₀ : (a.den: ℤ) ∣ a.num * b.den := by rw [h]; apply Int.dvd_mul_left
  have h₁ : (b.den: ℤ) ∣ b.num * a.den := by rw [←h]; apply Int.dvd_mul_left
  rw [←Int.dvd_gcd_mul_gcd_iff_dvd_mul, Int.gcd_comm] at h₀ h₁
  rw [ha] at h₀; rw [hb] at h₁
  rw [natCast_one, one_mul, Int.gcd_natCast_natCast, int_natCast_dvd_natCast] at h₀ h₁
  rw [Nat.gcd_comm] at h₁
  have := Nat.dvd_antisymm h₀ (Nat.gcd_dvd_left _ _)
  rw [←Nat.dvd_antisymm h₁ (Nat.gcd_dvd_right _ _)] at this
  clear h₀ h₁
  replace h : _ = _ := h
  rw [←this] at h
  have := of_mul_right₀ ?_ h
  ext <;> assumption
  intro h
  exact a.den_ne_zero (Int.ofNat.inj h)

def sound {a b: Fract} : a ≈ b -> mk a = mk b := by
  intro h
  apply toFract_inj
  apply is_reduced_spec
  apply (mk a).reduced
  apply (mk b).reduced
  apply Relation.trans (mk_rel _)
  apply Relation.trans h
  apply Relation.symm (mk_rel _)

@[simp] def mk_toFract (a: ℚ) : mk a.toFract = a := by
  apply toFract_inj
  apply is_reduced_spec
  exact (mk _).reduced
  exact a.reduced
  apply mk_rel

def exact {a b: Fract} : mk a = mk b -> a ≈ b := by
  intro h
  apply Relation.trans
  apply Relation.symm
  apply mk_rel
  rw [h]
  apply mk_rel

def lift (f: Fract -> α) (_: ∀a b, a ≈ b -> f a = f b) (a: ℚ) : α := f a.toFract
@[simp] def lift_mk (f: Fract -> α) (h) (a: Fract) : lift f h (mk a) = f a := by
  apply h
  apply mk_rel

def lift₂ (f: Fract -> Fract -> α) (_: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: ℚ) : α := f a.toFract b.toFract
@[simp] def lift₂_mk (f: Fract -> Fract -> α) (h) (a b: Fract) : lift₂ f h (mk a) (mk b) = f a b := by
  apply h
  apply mk_rel
  apply mk_rel

def lift_with (P: ℚ -> Prop) (f: ∀q, P (mk q) -> α) (_: ∀a b (ha: P (mk a)) (hb: P (mk b)), a ≈ b -> f a ha = f b hb) (a: ℚ) (ha: P a) : α := f a.toFract (by
    rwa [show mk a.toFract = a from ?_]
    simp)
@[simp] def lift_with_mk (P: ℚ -> Prop) (f: ∀q, P (mk q) -> α) (h) (a: Fract) (ha: P (mk a)) : lift_with P f h (mk a) ha = f a ha := by
  apply h
  apply mk_rel

attribute [irreducible] lift lift₂ lift_with

@[induction_eliminator]
def ind {motive: ℚ -> Prop} (mk: ∀q, motive (mk q)) (q: ℚ) : motive q := by
  rw [show q = Rational.mk q.toFract from ?_]
  apply mk
  simp

instance : Add Fract where
  add a b := {
    num := a.num * b.den + b.num * a.den
    den := a.den * b.den
    den_ne_zero := by
      intro h; rcases of_mul_eq_zero h with h | h
      exact a.den_ne_zero h
      exact b.den_ne_zero h
  }

@[simp] def Fract.add_num (a b: Fract) : (a + b).num = a.num * b.den + b.num * a.den := rfl
@[simp] def Fract.add_den (a b: Fract) : (a + b).den = a.den * b.den := rfl

instance : Add ℚ where
  add := lift₂ (fun a b => mk (a + b)) <| by
    intro a b c d ac bd
    apply sound; show _ = _; dsimp
    rw [add_mul, add_mul, mul_assoc, mul_left_comm (b.den: ℤ),
      ←mul_assoc, ac, mul_assoc c.num (d.den: ℤ), mul_left_comm (d.den: ℤ),
      ←mul_assoc c.num, mul_comm (b.den: ℤ)]
    congr 1
    rw [mul_comm (c.den: ℤ), mul_assoc, mul_left_comm (a.den: ℤ),
      ←mul_assoc, bd]
    rw [mul_comm _ (c.den: ℤ), mul_assoc _ (c.den: ℤ), mul_comm (a.den: ℤ),
      mul_left_comm (c.den: ℤ), ←mul_assoc (d.num)]

@[simp] def mk_add (a b: Fract) : mk a + mk b = mk (a + b) := by
  show lift₂ _ _ _ _ = _; simp

instance : Mul Fract where
  mul a b := {
    num := a.num * b.num
    den := a.den * b.den
    den_ne_zero := by
      intro h; rcases of_mul_eq_zero h with h | h
      exact a.den_ne_zero h
      exact b.den_ne_zero h
  }

@[simp] def Fract.mul_num (a b: Fract) : (a * b).num = a.num * b.num := rfl
@[simp] def Fract.mul_den (a b: Fract) : (a * b).den = a.den * b.den := rfl

instance : Mul ℚ where
  mul := lift₂ (fun a b => mk (a * b)) <| by
    intro a b c d ac bd
    apply sound; show _ = _; dsimp
    rw [mul_assoc, mul_left_comm b.num, ←mul_assoc,
      mul_assoc c.num, mul_left_comm d.num, ←mul_assoc c.num]
    congr 1

@[simp] def mk_mul (a b: Fract) : mk a * mk b = mk (a * b) := by
  show lift₂ _ _ _ _ = _; simp

instance : IntCast Fract where
  intCast n := {
    num := n
    den := 1
    den_ne_zero := by decide
  }

instance : IntCast ℚ where
  intCast n := {
    toFract:= n
    reduced := Int.gcd_one
  }

@[simp] def mk_intCast (n: ℤ) : mk n = n := by
  apply toFract_inj
  apply is_reduced_spec
  apply (mk _).reduced
  apply (n: ℚ).reduced
  apply mk_rel

instance : NatCast Fract where
  natCast n := (n: ℤ)

instance : NatCast ℚ where
  natCast n := (n: ℤ)

@[simp] def mk_natCast (n: ℕ) : mk n = n := by
  apply mk_intCast

instance : OfNat Fract n := ⟨n⟩
instance : OfNat ℚ n := ⟨n⟩

@[simp] def eq_zero_of_num_eq_zero (q: ℚ) : q.num = 0 -> q = 0 := by
  obtain ⟨⟨n, d, dnz⟩, g⟩ := q
  dsimp [Fract.is_reduced] at g
  dsimp
  intro rfl
  congr
  rwa [Int.gcd_zero_left, Int.natAbs_natCast] at g

instance : SMul ℤ ℚ where
  smul a b := a * b
instance : SMul ℕ ℚ where
  smul a b := a * b

def not_eqv_zero_of_mk_ne_zero {a: Fract} : mk a ≠ 0 -> ¬(a ≈ 0) := by
  intro h g; apply h
  show _ = mk 0
  apply sound
  assumption

macro_rules
| `(tactic|invert_tactic_trivial) => `(tactic|apply not_eqv_zero_of_mk_ne_zero <;> invert_tactic)

instance : CheckedInv Fract (fun x => ¬(x ≈ 0)) where
  checked_inv a ha := {
    num := a.num.sign * a.den
    den := a.num.natAbs
    den_ne_zero := by
      intro h; replace ha : _ ≠ _ := ha
      rw [Int.natAbs_eq_zero.mp h, zero_mul,
        show Fract.num 0 = 0 from rfl,
        zero_mul] at ha
      contradiction
  }

@[simp] def Fract.inv_num (a: Fract) (ha: ¬a ≈ 0) : (a⁻¹?).num = a.num.sign * a.den := rfl
@[simp] def Fract.inv_den (a: Fract) (ha: ¬a ≈ 0) : (a⁻¹?).den = a.num.natAbs := rfl

instance : CheckedInv? ℚ where
  checked_inv a ha := {
    toFract := a.toFract⁻¹?~(by
      intro h; replace h := sound h
      rw [mk_toFract] at h
      apply ha; rw [h]; rfl)
    reduced := by
      show _ = _
      rw [Int.gcd_comm]
      show (a.num.natAbs: ℤ).gcd (a.num.sign * a.den) = 1
      rw [←Int.mul_sign_self, mul_comm, Int.gcd_mul_left,
        a.reduced]
      rw [Int.natAbs_sign_of_ne_zero]
      intro h
      apply ha
      apply eq_zero_of_num_eq_zero
      assumption
  }

def inv_congr (a b: Fract) (h: a ≈ b) (ha: ¬a ≈ 0) (hb: ¬b ≈ 0) : a⁻¹? ≈ b⁻¹? := by
  show _ = _
  simp
  rw [←Int.natAbs_natCast a.den,
    mul_assoc, ←natCast_mul,
    ←Int.natAbs_mul, mul_comm _ b.num, ←h,
    Int.natAbs_mul, natCast_mul, ←mul_assoc,
    Int.sign_mul_natAbs, Int.natAbs_natCast]
  rw [←Int.natAbs_natCast b.den,
    mul_assoc, ←natCast_mul,
    ←Int.natAbs_mul, mul_comm _ a.num, h,
    Int.natAbs_mul, natCast_mul, ←mul_assoc,
    Int.sign_mul_natAbs, Int.natAbs_natCast,
    Int.natAbs_natCast, h]

def mk_inv? (a: Fract) (ha: mk a ≠ 0) : (mk a)⁻¹? = mk (a⁻¹?) := by
  apply toFract_inj
  show _⁻¹?~(_) = _
  apply is_reduced_spec
  apply ((mk a)⁻¹?).reduced
  apply (mk _).reduced
  apply flip Relation.trans
  apply Relation.symm
  apply mk_rel
  apply inv_congr
  apply mk_rel

instance : Pow Fract ℕ where
  pow a n := {
    num := a.num ^ n
    den := a.den ^ n
    den_ne_zero := by
      intro h
      apply a.den_ne_zero
      induction n with
      | zero => contradiction
      | succ n ih =>
        rw [npow_succ] at h
        cases of_mul_eq_zero h
        apply ih; assumption
        assumption
  }

@[simp] def Fract.npow_num (a: Fract) (n: ℕ) : (a ^ n).num = a.num ^ n := rfl
@[simp] def Fract.npow_den (a: Fract) (n: ℕ) : (a ^ n).den = a.den ^ n := rfl

-- private def of_dvd_one (a: ℤ) : a ∣ 1 -> a = 1 ∨ a = -1 := by
--   intro h
--   rcases Int.le_total a 0 with g | g
--   right
--   have := Int.eq_one_of_dvd_one (Int.neg_le_neg g) (by rwa [Int.neg_dvd])
--   rw [←this, neg_neg]
--   left; apply Int.eq_one_of_dvd_one <;> assumption

-- private def of_dvd_pow (a b: ℤ) (n: ℕ) : a ∣ b ^ n -> a ∣ b ∨ (a = 1 ∨ a = -1) := by
--   intro ha
--   obtain ⟨k, h⟩ := ha
--   have htemp₀ (a k: ℕ) : 1 ≠ (a + 2) * (k + 1) := by
--     rw [mul_add, add_mul, add_mul]
--     simp only [←add_assoc]; intro h
--     have : 2 ≤ 1 := by rw [h]; apply Nat.le_add_left
--     contradiction
--   have htemp₁ (a k: ℕ) : (1: ℤ) ≠ -((a + 2) * k: ℕ) := by
--     intro h
--     have := Int.zero_lt_one
--     rw [h] at this
--     exact Int.not_le.mpr this (Int.neg_natCast_le_ofNat _ _)
--   induction n generalizing k with
--   | zero =>
--     simp at h
--     match a with
--     | 1 | -1 => right; decide
--     | 0 => rw [zero_mul] at h; contradiction
--     | (a + 2: ℕ) =>
--       match k with
--       | 0 => rw [mul_zero] at h; contradiction
--       | (k + 1: ℕ) =>
--         rw [←natCast_mul] at h
--         have := Int.ofNat.inj h
--         exfalso; apply htemp₀
--         assumption
--       | -(k + 1: ℕ) =>
--         exfalso
--         rw [←neg_mul_right, ←natCast_mul] at h
--         apply htemp₁
--         assumption
--     | -(a + 2: ℕ) =>
--       rw [←neg_mul_left] at h
--       exfalso
--       match k with
--       | (k: ℕ) =>
--         rw [←natCast_mul] at h
--         apply htemp₁
--         assumption
--       | -(k + 1: ℕ) =>
--         rw [neg_mul_right, neg_neg, ←natCast_mul] at h
--         replace h := Int.ofNat.inj h
--         apply htemp₀
--         assumption
--   | succ n ih =>
--     rw [npow_succ] at h

--     sorry
--     -- rcases ih with ih | ih
--     -- · sorry
--     -- sorry

-- #axiom_blame of_dvd_pow

-- instance : Pow ℚ ℕ where
--   pow a n := {
--     toFract := a.toFract ^ n
--     reduced := by
--       show Int.gcd _ _ = _
--       simp
--       obtain ⟨⟨num, den, dnz⟩, h⟩ := a
--       dsimp; rename_i h; clear h
--       dsimp [Fract.is_reduced] at h
--       refine Int.gcd_eq_one_iff.mpr ?_
--       intro k hk₀ hk₁
--       refine if hk:k = 1 ∨ k = -1 then ?_ else ?_
--       rcases hk with rfl | rfl <;> decide
--       simp at hk

--       have numk : num ∣ k := by
--         obtain ⟨k', hk'⟩ := hk₀
--         sorry
--       have denk : (den: ℤ) ∣ k := by
--         sorry
--       sorry
--       -- induction n with
--       -- | zero => simp
--       -- | succ n ih =>
--       --   simp [npow_succ]
--   }

-- #print axioms instPowNat

-- instance : CheckedDiv? ℚ where
--   checked_div a b hb := a * b⁻¹?

-- instance : CheckedZPow? ℚ where
--   checked_pow a n ha :=
--     match n with
--     | .ofNat n => sorry
--     | .negSucc n => (a⁻¹?) ^ (n + 1)

end Rational
