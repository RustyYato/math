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
  suffices (mk a).toFract = (mk b).toFract by
    unfold mk
    dsimp; congr 1
  apply is_reduced_spec
  apply (mk a).reduced
  apply (mk b).reduced
  apply Relation.trans (mk_rel _)
  apply Relation.trans h
  apply Relation.symm (mk_rel _)

def lift (f: Fract -> α) (_: ∀a b, a ≈ b -> f a = f b) (a: ℚ) : α := f a.toFract
@[simp] def lift_mk (f: Fract -> α) (h) (a: Fract) : lift f h (mk a) = f a := by
  apply h
  apply mk_rel

def lift₂ (f: Fract -> Fract -> α) (_: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: ℚ) : α := f a.toFract b.toFract
@[simp] def lift₂_mk (f: Fract -> Fract -> α) (h) (a b: Fract) : lift₂ f h (mk a) (mk b) = f a b := by
  apply h
  apply mk_rel
  apply mk_rel

attribute [irreducible] lift lift₂

@[induction_eliminator]
def ind {motive: ℚ -> Prop} (mk: ∀q, motive (mk q)) (q: ℚ) : motive q := by
  rw [show q = Rational.mk q.toFract from ?_]
  apply mk
  suffices q.toFract = (Rational.mk q.toFract).toFract by
    cases q; congr
  apply is_reduced_spec
  exact q.reduced
  exact (Rational.mk q.toFract).reduced
  apply Relation.symm
  apply mk_rel

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

def mk_add (a b: Fract) : mk a + mk b = mk (a + b) := by
  show lift₂ _ _ _ _ = _; simp

end Rational
