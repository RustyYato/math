module

public import Math.Algebra.Monoid.Char
public import Math.Algebra.Semiring.Defs
public import Math.Tactic.Invert

namespace Math

variable [SemiringOps α] [IsSemiring α]

public theorem of_natCast_eq_zero (n: ℕ)  (h: (n: α) = 0) (g: ∀m: ℕ, (m: α) = 0 -> n ∣ m) : HasChar α n where
  nsmul_eq_zero_iff_dvd m := by
    apply Iff.intro
    · intro h'
      apply g
      rw [←mul_one (m: α), ←nsmul_eq_natCast_mul, h']
    · rintro ⟨k, rfl⟩ a
      rw [mul_nsmul, nsmul_eq_mul_natCast,
        nsmul_eq_mul_natCast, h, mul_zero]

public theorem natCast_eq_zero (α: Type*) [SemiringOps α] [IsSemiring α] [HasChar α n] : (n: α) = 0 := by
  rw [←mul_one (n: α), ←nsmul_eq_natCast_mul, nsmul_eq_zero]
  apply Nat.dvd_refl

public theorem dvd_of_natCast_eq_zero [HasChar α n] (m: ℕ) (hm: m = (0: α)) : n ∣ m := by
  apply (HasChar.nsmul_eq_zero_iff_dvd (α := α) _).mp
  intro a
  rw [nsmul_eq_mul_natCast, hm, mul_zero]

public theorem dvd_of_ring_hom
  [SemiringOps β] [IsSemiring β]
  [HasChar α n] [HasChar β m]
  (f: α →+* β) : m ∣ n := by
  apply HasChar.char_dvd (α := β)
  intro b; rw [←one_mul b, nsmul_eq_natCast_mul, ←mul_assoc, ←nsmul_eq_natCast_mul,
    ←map_one f, ←map_nsmul, nsmul_one_eq_natCast, natCast_eq_zero, map_zero, zero_mul]

public theorem of_ring_emb [SemiringOps β] [IsSemiring β] [HasChar α n]
  (f: α ↪+* β) : HasChar β n := by
  apply of_natCast_eq_zero
  rw [←map_natCast f, natCast_eq_zero, map_zero]
  intro m hn
  apply dvd_of_natCast_eq_zero (α := α)
  rw [←map_natCast f, ←map_zero f] at hn
  exact f.inj hn

public theorem of_ring_equiv
  [SemiringOps β] [IsSemiring β] [HasChar β n] (f: α ≃+* β) : HasChar α n :=
  of_ring_emb { f.symm.toRingHom with injective := f.symm.inj }

public theorem natCast_inj [IsLeftAddCancel α] [HasChar α 0]: Function.Injective (Nat.cast (R := α)) := by
  suffices ∀n m: ℕ, (n: α) = m -> n ≤ m -> n = m by
    intro n m eq
    rcases Nat.le_total n m with h | h
    apply this
    assumption
    assumption
    symm; apply this
    symm; assumption
    assumption
  intro a b h a_le_b
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le a_le_b
  rw [←add_zero (a: α), natCast_add] at h
  replace h := of_add_left h
  rw (occs := [1]) [←add_zero a]
  congr 1; clear a_le_b; symm
  exact Nat.zero_dvd.mp (dvd_of_natCast_eq_zero _ h.symm)

public theorem two_ne_zero [nc: NontrivialChar α n] : ((2: ℕ): α) ≠ 0 := by
  intro h
  exact nc.n_not_dvd_two (dvd_of_natCast_eq_zero _ h)

instance [nc: NontrivialChar α n] : NeZero ((2: ℕ): α) where
  out := two_ne_zero

macro_rules
| `(tactic|invert_tactic_trivial) => `(apply two_ne_zero)
