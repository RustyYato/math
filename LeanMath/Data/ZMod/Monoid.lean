import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.ZMod.Semigroup
import LeanMath.Algebra.Monoid.Char

instance : IsLawfulOneMul (ZMod n) where
  one_mul a := by
    apply ZMod.val_inj.mp; simp
    rw [
        Int.mul_emod, Int.emod_emod,
        ←Int.mul_emod, one_mul, a.mod_eq_self]
  mul_one a := by
    apply ZMod.val_inj.mp; simp
    rw [Int.mul_emod, Int.emod_emod,
        ←Int.mul_emod, mul_one, a.mod_eq_self]

-- use the default which optimizes to pown by squaring, which is very fast
-- even for 1000 bit powers. This method also ensures that we don't
-- overflow the limit, which could happen if we naively just did pow n
-- by lowering to nat pow n
instance : Pow (ZMod n) ℕ := defaultPowN

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
  npow_zero _ := rfl
  npow_succ _ _ := rfl

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
