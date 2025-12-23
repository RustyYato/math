import LeanMath.Algebra.Group.Defs

def ZMod : ℕ -> Type
| 0 => ℤ
| n + 1 => Fin (n + 1)

namespace ZMod

instance : ∀n, Zero (ZMod n)
| 0 => inferInstanceAs (Zero ℤ)
| n + 1 => inferInstanceAs (Zero (Fin (n + 1)))
instance : ∀n, Add (ZMod n)
| 0 => inferInstanceAs (Add ℤ)
| n + 1 => inferInstanceAs (Add (Fin (n + 1)))
instance : ∀n, SMul ℕ (ZMod n)
| 0 => inferInstanceAs (SMul ℕ ℤ)
| n + 1 => inferInstanceAs (SMul ℕ (Fin (n + 1)))

instance : ∀n, Neg (ZMod n)
| 0 => inferInstanceAs (Neg ℤ)
| n + 1 => inferInstanceAs (Neg (Fin (n + 1)))
instance : ∀n, Sub (ZMod n)
| 0 => inferInstanceAs (Sub ℤ)
| n + 1 => inferInstanceAs (Sub (Fin (n + 1)))
instance : ∀n, SMul ℤ (ZMod n)
| 0 => inferInstanceAs (SMul ℤ ℤ)
| n + 1 => inferInstanceAs (SMul ℤ (Fin (n + 1)))

instance : NatCast (Fin (n + 1)) := Fin.NatCast.instNatCast _

@[local simp] def Fin.natCast_def (n k: ℕ) : (Nat.cast k: Fin (n + 1)) = ⟨k % (n + 1), by apply Nat.mod_lt; apply Nat.zero_lt_succ⟩ := rfl

private def instAddGroupSucc : IsAddGroup (ZMod (n + 1)) where
  add_assoc := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    repeat rw [Fin.add_def]
    simp [add_assoc]
  zero_add := by
    intro ⟨a, ha⟩
    repeat rw [Fin.add_def]
    simp
    congr
    rw [Nat.mod_eq_of_lt ha]
  add_zero := by
    intro ⟨a, ha⟩
    repeat rw [Fin.add_def]
    simp
    congr
    rw [Nat.mod_eq_of_lt ha]
  sub_eq_add_neg := by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    repeat rw [Fin.add_def]
    rw [Fin.sub_def, Fin.neg_def]
    simp
    congr 1
    rw [add_comm a]
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul a k := by
    obtain ⟨a, ha⟩ := a
    -- show Fin.mk _ _ = Fin.mk _ _
    -- simp only [Fin.IntCast.instIntCast, Fin.intCast, Int.negSucc_not_nonneg, ↓reduceIte, Fin.ofNat,
    --   Int.natAbs_negSucc, Nat.succ_eq_add_one, Fin.neg_def, Nat.mod_mul_mod, HSMul.hSMul, SMul.smul,
    --   Fin.natCast_def, Fin.mul_def, Fin.mk.injEq]
    -- apply Int.natCast_inj.mp
    -- simp
    rw [←SMul.smul_eq_hSMul, ←SMul.smul_eq_hSMul]
    simp [SMul.smul]
    simp [Fin.neg_def, Fin.mul_def, Fin.intCast_def]
    congr 1
    simp
    apply Int.natCast_inj.mp
    simp
    repeat rw [Int.ofNat_sub (by
      apply Nat.le_of_lt
      apply Nat.mod_lt
      apply Nat.zero_lt_succ)]
    simp
    conv => {
      lhs;
      rw [Int.mul_emod, Int.sub_emod, Int.emod_emod,
        ←Int.emod_emod (n + 1),
        Int.emod_self, ←Int.sub_emod, ←Int.mul_emod, Int.zero_sub]
    }
    rw [Int.neg_emod_eq_sub_emod]
    conv => {
      rhs;
      rw [Int.sub_emod, Int.emod_emod,
        ←Int.sub_emod, ←Int.neg_emod_eq_sub_emod]
    }
    rw [Int.neg_mul]
  zero_nsmul a := by
    show Fin.mk _ _ = Fin.mk _ _
    simp [Fin.NatCast.instNatCast]
  succ_nsmul a n := by
    show Fin.mk _ _ = Fin.mk _ _
    simp [Fin.NatCast.instNatCast]
    rw [Nat.succ_mul]
  add_neg_cancel a := by
    show Fin.mk _ _ = Fin.mk _ _
    simp

private def instAddGroup0 : IsAddGroup (ZMod 0) := inferInstanceAs (IsAddGroup ℤ)
instance : ∀n, IsAddGroup (ZMod n)
| 0 => instAddGroup0
| _ + 1 => instAddGroupSucc

@[local simp] def Fin.nsmul_def (k n: ℕ) (a: Fin (n + 1)) : k • a = ⟨(k * a) % (n + 1), by apply Nat.mod_lt; apply Nat.zero_lt_succ⟩ := by
  show Fin.mk _ _ = _
  simp [Fin.NatCast.instNatCast]

def nsmul_eq_zero (a: ZMod n) : n • a = 0 := by
  cases n
  rw [zero_nsmul]
  rename_i n
  rw [Fin.nsmul_def]
  simp

end ZMod
