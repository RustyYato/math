import LeanMath.Data.Rational.Order
import LeanMath.Algebra.Archimedean.Field
import LeanMath.Algebra.Char0Field.Defs

def ratCast_le_ratCast [LE α] [LT α] [FieldOps α] [RatCast α] [IsZeroLEOne α]
  [IsChar0Field α] [IsOrderedSemiring α] [IsLinearOrder α] {a b: ℚ} : (a: α) ≤ (b: α) ↔ a ≤ b := by
  cases a using Rational.ind with | _ a =>
  cases b using Rational.ind with | _ b =>
  show _ ↔ Rational.IsNonneg _
  rw [ratCast_mk, ratCast_mk, Rational.mk_sub, Rational.mk_nonneg,
    Rational.Fract.IsNonneg, Rational.Fract.sub_num, le_sub_iff_add_le, zero_add]
  apply Iff.trans _ (intCast_le_intCast (α := α) _ _)
  rw [intCast_mul, intCast_mul, intCast_ofNat, intCast_ofNat]
  apply Iff.intro
  · intro h
    have := mul_le_mul_of_nonneg_right h (a.den) ?_
    rw [div?_mul_cancel, div?_eq_mul_inv?, mul_comm_right] at this
    have := mul_le_mul_of_nonneg_right this (b.den) ?_
    rw [mul_assoc, inv?_mul_cancel, mul_one] at this
    assumption
    rw [←natCast_zero]
    apply (natCast_le_natCast _ _).mpr
    exact le_of_lt b.den_pos
    rw [←natCast_zero]
    apply (natCast_le_natCast _ _).mpr
    exact le_of_lt a.den_pos
  · intro h
    rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
    rw [←mul_one (a.num: α), ←mul_inv?_cancel (b.den: α)]
    rw [←mul_assoc, mul_assoc (_ * _)]
    apply le_trans
    apply mul_le_mul_of_nonneg_right
    assumption
    rw [←inv?_mul_rev]
    apply le_of_lt
    apply pos_inv?
    rw [←natCast_mul, ←natCast_zero]
    apply (natCast_lt_natCast _ _).mpr
    apply mul_pos; exact a.den_pos; exact b.den_pos
    have := a.den_ne_zero
    have := b.den_ne_zero
    intro h; rw [←natCast_zero, ←natCast_mul, HasChar.natCast_inj.eq_iff] at h
    cases of_mul_eq_zero h <;> contradiction
    rw [mul_comm (_⁻¹?~(_)), mul_assoc, ←mul_assoc (a.den: α), mul_inv?_cancel, one_mul]
    intro h; rw [←natCast_zero, HasChar.natCast_inj.eq_iff] at h
    exact b.den_ne_zero h

def ratCast_lt_ratCast [LE α] [LT α] [FieldOps α] [RatCast α] [IsZeroLEOne α]
  [IsChar0Field α] [IsOrderedSemiring α] [IsLinearOrder α] {a b: ℚ} : (a: α) < (b: α) ↔ a < b := by
  cases a using Rational.ind with | _ a =>
  cases b using Rational.ind with | _ b =>
  show _ ↔ Rational.IsPos _
  rw [ratCast_mk, ratCast_mk, Rational.mk_sub, Rational.mk_pos,
    Rational.Fract.IsPos, Rational.Fract.sub_num, lt_sub_iff_add_lt, zero_add]
  apply Iff.trans _ (intCast_lt_intCast (α := α) _ _)
  rw [intCast_mul, intCast_mul, intCast_ofNat, intCast_ofNat]
  apply Iff.intro
  · intro h
    have := mul_lt_mul_of_pos_right _ _ h (a.den) ?_
    rw [div?_mul_cancel, div?_eq_mul_inv?, mul_comm_right] at this
    have := mul_lt_mul_of_pos_right _ _ this (b.den) ?_
    rw [mul_assoc, inv?_mul_cancel, mul_one] at this
    assumption
    rw [←natCast_zero]
    apply (natCast_lt_natCast _ _).mpr
    exact b.den_pos
    rw [←natCast_zero]
    apply (natCast_lt_natCast _ _).mpr
    exact a.den_pos
  · intro h
    rw [div?_eq_mul_inv?, div?_eq_mul_inv?]
    rw [←mul_one (a.num: α), ←mul_inv?_cancel (b.den: α)]
    rw [←mul_assoc, mul_assoc (_ * _)]
    apply lt_of_lt_of_le
    apply mul_lt_mul_of_pos_right
    assumption
    rw [←inv?_mul_rev]
    apply pos_inv?
    rw [←natCast_mul, ←natCast_zero]
    apply (natCast_lt_natCast _ _).mpr
    apply mul_pos; exact a.den_pos; exact b.den_pos
    have := a.den_ne_zero
    have := b.den_ne_zero
    intro h; rw [←natCast_zero, ←natCast_mul, HasChar.natCast_inj.eq_iff] at h
    cases of_mul_eq_zero h <;> contradiction
    rw [mul_comm (_⁻¹?~(_)), mul_assoc, ←mul_assoc (a.den: α), mul_inv?_cancel, one_mul]
    intro h; rw [←natCast_zero, HasChar.natCast_inj.eq_iff] at h
    exact b.den_ne_zero h

instance : IsArchimedean ℚ := by
  apply archimedean_iff_nat_lt.mpr
  intro x
  cases x using Rational.ind with | mk x =>
  exists x.num.natAbs + 1
  show Rational.cast (Rational.mk x) < _
  rw [ratCast_mk]
  apply lt_of_mul_lt_mul_of_pos_right
  show 0 < (x.den: ℚ)
  rw [←natCast_zero]; apply (natCast_lt_natCast _ _).mpr
  exact x.den_pos
  rw [div?_mul_cancel]
  rw [←natCast_mul, ←intCast_ofNat]
  apply (intCast_lt_intCast _ _).mpr
  rw [natCast_mul]
  apply lt_of_lt_of_le
  show x.num < (x.num.natAbs + 1: ℕ)
  · apply lt_of_le_of_lt
    apply Int.le_natAbs
    apply Int.ofNat_lt.mpr
    apply Nat.lt_succ_self
  rw (occs := [1]) [←add_zero ((x.num.natAbs + 1: ℕ): ℤ), add_comm]
  apply add_le_iff_le_sub.mpr
  cases h:x.den with
  | zero => nomatch x.den_ne_zero h
  | succ n =>
    rw [←nsmul_eq_mul_natCast, succ_nsmul, add_sub_assoc, sub_self, add_zero]
    rw [nsmul_eq_mul_natCast, ←natCast_mul]
    apply Int.natCast_nonneg

def archimedean_iff_rat_le [LE α] [LT α] [FieldOps α] [RatCast α] [IsZeroLEOne α]
  [IsChar0Field α] [IsOrderedSemiring α] [IsLinearOrder α] : IsArchimedean α ↔ ∀ x : α, ∃ n : ℚ, x ≤ n := by
  apply Iff.trans archimedean_iff_int_le
  apply Iff.intro
  · intro h x
    have ⟨n, hn⟩ := h x
    exists n
    show x ≤ ratCastHom n
    rwa [map_intCast]
  · intro h x
    have ⟨n, hn⟩ := h x
    have ⟨m, hm⟩  := archimedean_iff_int_lt.mp (inferInstance: IsArchimedean ℚ) n
    exists m
    apply le_trans; assumption
    show ratCastHom n ≤ _
    rw [←map_intCast ratCastHom]
    show Rational.cast n ≤ Rational.cast _
    apply ratCast_le_ratCast.mpr
    apply le_of_lt
    assumption

def archimedean_iff_rat_lt [LE α] [LT α] [FieldOps α] [RatCast α] [IsZeroLEOne α]
  [IsChar0Field α] [IsOrderedSemiring α] [IsLinearOrder α] : IsArchimedean α ↔ ∀ x : α, ∃ n : ℚ, x < n := by
  apply Iff.trans archimedean_iff_int_lt
  apply Iff.intro
  · intro h x
    have ⟨n, hn⟩ := h x
    exists n
    show x < ratCastHom n
    rwa [map_intCast]
  · intro h x
    have ⟨n, hn⟩ := h x
    have ⟨m, hm⟩  := archimedean_iff_int_lt.mp (inferInstance: IsArchimedean ℚ) n
    exists m
    apply lt_trans; assumption
    show ratCastHom n < _
    rw [←map_intCast ratCastHom]
    show Rational.cast n < Rational.cast _
    apply ratCast_lt_ratCast.mpr
    assumption
