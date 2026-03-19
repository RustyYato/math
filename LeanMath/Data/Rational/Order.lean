import LeanMath.Data.Rational.Defs
import LeanMath.Order.Defs

namespace Rational

def Fract.IsNonneg (a: Fract) : Prop := 0 ≤ a.num
def Fract.IsPos (a: Fract) : Prop := 0 < a.num

def IsNonneg (a: ℚ) : Prop := 0 ≤ a.num
def IsPos (a: ℚ) : Prop := 0 < a.num

private def mk_nonneg' (a b: Fract) (h: a ≈ b) : a.IsNonneg ↔ b.IsNonneg := by
  replace h : _ = _ := h
  simp [Fract.IsNonneg]
  obtain ⟨a, a', ha⟩ := a
  obtain ⟨b, b', hb⟩ := b
  dsimp at h; dsimp
  cases a <;> cases b
  any_goals simp
  · simp [Int.negSucc_mul_ofNat] at h
    rw [←natCast_mul] at h
    match a', b' with
    | _ + 1, _ + 1 =>
    contradiction
  · simp [Int.negSucc_mul_ofNat] at h
    rw [←natCast_mul] at h
    match a', b' with
    | _ + 1, _ + 1 =>
    contradiction
def mk_nonneg (a: Fract) : (mk a).IsNonneg ↔ a.IsNonneg := by
  apply mk_nonneg'
  apply mk_rel

instance : LE ℚ where
  le a b := (b - a).IsNonneg
instance : LT ℚ where
  lt a b := (b - a).IsPos

instance : IsLinearOrder ℚ where
  lt_iff_le_and_not_ge {a b} := by
    show IsPos _ ↔ IsNonneg _ ∧ ¬IsNonneg  _
    apply Iff.intro
    intro h
    apply And.intro
    apply le_of_lt; assumption
    apply not_le_of_lt
    apply Int.neg_lt_neg_iff.mp
    show 0 < (-(a - b)).num
    rwa [neg_sub]
    intro ⟨h, g⟩
    rcases lt_or_eq_of_le h with h | h
    assumption
    exfalso
    cases (sub_eq_zero _ _).mpr ( eq_zero_of_num_eq_zero _ h.symm)
    apply g; show 0 ≤ _; rw [sub_self]; rfl
  refl a := by show 0 ≤ (a - a).num; rw [sub_self]; rfl
  trans {a b c} h g := by
    replace h : IsNonneg _ := h
    replace g : IsNonneg _ := g
    show IsNonneg _
    induction a using ind with | mk a =>
    induction b using ind with | mk b =>
    induction c using ind with | mk c =>
    simp [mk_nonneg] at *
    simp [Fract.IsNonneg] at *
    have h₀ :=
      Int.mul_le_mul_of_nonneg_left h (Int.natCast_nonneg c.den)
    rw [mul_left_comm _ (b.num), ←mul_assoc b.num] at h₀
    have h₁ :=
      Int.mul_le_mul_of_nonneg_right g (Int.natCast_nonneg a.den)
    replace h := le_trans h₀ h₁
    clear h₀ h₁ g
    rw [mul_comm_right, ←mul_assoc, mul_comm (c.den: ℤ)] at h
    apply Int.le_of_mul_le_mul_right h
    apply Int.ofNat_lt.mpr
    exact b.den_pos
  total := by
    intro a b
    rcases le_total 0 (b - a).num with h | h
    · left
      assumption
    · right
      have : 0 ≤ (-(b - a)).num := Int.neg_le_neg_iff.mpr h
      rwa [neg_sub] at this
  antisymm {a b} h g := by
    replace h : 0 ≤ (b - a).num := h
    replace g : 0 ≤ (a - b).num := g
    rw [←Int.neg_le_neg_iff] at g
    replace g : (-(a - b)).num ≤ 0 := g
    rw [neg_sub] at g
    have := le_antisymm (α := ℤ) g h
    rw [(sub_eq_zero _ _).mpr (eq_zero_of_num_eq_zero _ this)]

instance : DecidableRel (· ≤ ·: ℚ -> ℚ -> Prop) :=
  fun a b => decidable_of_iff (0 ≤ (b - a).num) Iff.rfl
instance : DecidableRel (· < ·: ℚ -> ℚ -> Prop) :=
  fun a b => decidable_of_iff (0 < (b - a).num) Iff.rfl

instance : Min ℚ := minOfLe
instance : Max ℚ := maxOfLe

def min_eq (a b: ℚ) : a ⊓ b = if a ≤ b then a else b := rfl
def max_eq (a b: ℚ) : a ⊔ b = if a ≤ b then b else a := rfl

instance : IsLattice ℚ where
  left_le_max {_ _} := by
    rw [max_eq]; split; assumption
    rfl
  right_le_max {_ _} := by
    rw [max_eq]; split; rfl
    apply le_of_lt; apply not_le.mp
    assumption
  max_le _ _ := by
    rw [max_eq]; split <;> assumption
  min_le_left {_ _} := by
    rw [min_eq]; split; rfl
    apply le_of_lt; apply not_le.mp
    assumption
  min_le_right {_ _} := by
    rw [min_eq]; split; assumption
    rfl
  le_min _ _ := by
    rw [min_eq]; split <;> assumption

end Rational
