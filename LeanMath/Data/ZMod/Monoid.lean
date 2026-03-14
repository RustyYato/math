import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.ZMod.Semigroup
import LeanMath.Algebra.Monoid.Char

instance : IsAddMonoid (ZMod n) where
  zero_add a := by
    apply ZMod.val_inj.mp; dsimp
    rw [zero_add, a.mod_eq_self]
  add_zero a := by
    apply ZMod.val_inj.mp; dsimp
    rw [add_zero, a.mod_eq_self]
  zero_nsmul a := by
    apply ZMod.val_inj.mp; dsimp
    rw [zero_mul, Int.zero_emod]
  succ_nsmul n a := by
    apply ZMod.val_inj.mp; dsimp
    rw [Int.add_mul, Int.one_mul,
      Int.add_emod, a.mod_eq_self]

instance : IsMonoid (ZMod n) where
  one_mul a := by
    apply ZMod.val_inj.mp; simp
    rw [
        Int.mul_emod, Int.emod_emod,
        ←Int.mul_emod, one_mul, a.mod_eq_self]
  mul_one a := by
    apply ZMod.val_inj.mp; simp
    rw [Int.mul_emod, Int.emod_emod,
        ←Int.mul_emod, mul_one, a.mod_eq_self]
  npow_zero a := by
    apply ZMod.val_inj.mp; simp
  npow_succ n a := by
    apply ZMod.val_inj.mp; dsimp
    rw [
      Int.pow_succ,
      Int.mul_emod (_ % _),
      Int.emod_emod,
      ←Int.mul_emod
    ]

instance : IsLawfulZeroMul (ZMod n) where
  zero_mul a := by
    apply ZMod.val_inj.mp; dsimp
    rw [zero_mul, Int.zero_emod]
  mul_zero a := by
    apply ZMod.val_inj.mp; dsimp
    rw [mul_zero, Int.zero_emod]

instance : HasChar (ZMod n) n where
  dvd_iff_nsmul_eq_zero k := by
    apply Iff.intro
    · rintro ⟨k, rfl⟩ a
      rw [mul_nsmul, ZMod.nsmul_eq_natCast_mul n,
        ZMod.natCast_degree, zero_mul, nsmul_zero]
    · intro h
      simp [ZMod.nsmul_eq_natCast_mul] at h
      rw [ZMod.natCast_eq_mod] at h
      rw [Nat.dvd_iff_mod_eq_zero]
      replace h := h 1
      rw [mul_one] at h
      replace h : ZMod.val (n := n) (k % n: ℕ) = 0 := by rw [h]; rfl
      dsimp at h
      rw [Int.emod_emod] at h
      rw [Int.ofNat_mod_ofNat] at h
      exact Int.ofNat.inj h
