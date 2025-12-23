import LeanMath.Algebra.Group.Free
import LeanMath.Data.ZMod.Defs

inductive Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (g: FreeGroup Unit) : Rel n (g ^ n) 1

-- the cyclic group of order n
def CyclicGroup (n: ℕ) := GroupQuot (Rel n)

namespace CyclicGroup

def ι : CyclicGroup n := GroupQuot.mk _ (FreeGroup.ι ())

instance : One (CyclicGroup n) := inferInstanceAs (One (GroupQuot _))
instance : Mul (CyclicGroup n) := inferInstanceAs (Mul (GroupQuot _))
instance : Inv (CyclicGroup n) := inferInstanceAs (Inv (GroupQuot _))
instance : Div (CyclicGroup n) := inferInstanceAs (Div (GroupQuot _))
instance : Pow (CyclicGroup n) ℕ := inferInstanceAs (Pow (GroupQuot _) ℕ)
instance : Pow (CyclicGroup n) ℤ := inferInstanceAs (Pow (GroupQuot _) ℤ)

instance : IsComm (CyclicGroup n) := inferInstanceAs (IsComm (GroupQuot _))
instance : IsGroup (CyclicGroup n) := inferInstanceAs (IsGroup (GroupQuot _))

def pown_eq_one (x: CyclicGroup n) : x ^ n = 1 := by
  induction x using GroupQuot.ind with | mk x =>
  induction x with
  | one => simp [map_one, one_npow]
  | inv x ih =>
    simp [map_inv]
    rw [←one_inv, ←ih]
    apply eq_inv_of_mul
    rw [←mul_npow, inv_mul_cancel, one_npow]
  | mul a b iha ihb =>
    rw [map_mul, mul_npow, iha, ihb, mul_one]
  | ι x =>
    apply GroupQuot.sound
    apply Rel.intro

def generated_by_ι (x: CyclicGroup n) : ∃k: ℤ, x = ι ^ k := by
  induction x using GroupQuot.ind with | mk x =>
  induction x with
  | one =>
    exists 0
    rw [zpow_zero, map_one]
  | ι x =>
    exists 1
    rw [zpow_one]
    rfl
  | inv a ih =>
    obtain ⟨k, ih⟩ := ih
    exists -k
    rw [map_inv, ih]
    symm; apply eq_inv_of_mul
    rw [←zpow_add, neg_add_cancel, zpow_zero]
  | mul a b ih₀ ih₁ =>
    obtain ⟨n, ih₀⟩ := ih₀
    obtain ⟨m, ih₁⟩ := ih₁
    exists n + m
    rw [map_mul, ih₀, ih₁]
    rw [zpow_add]

def generated_by_ι' [NeZero n] (x: CyclicGroup n) : ∃k < n, x = ι ^ k := by
  obtain ⟨k, ih⟩ := generated_by_ι x
  exists (k % n).toNat
  apply And.intro
  apply (Int.toNat_lt _).mpr
  apply Int.emod_lt
  apply NeZero.ne
  apply Int.emod_nonneg
  apply NeZero.ne
  rw [ih, ←zpow_ofNat, Int.ofNat_toNat, Int.max_eq_left]
  rw (occs := [1]) [←Int.mul_ediv_add_emod k n]
  rw [zpow_add, zpow_mul, zpow_ofNat, pown_eq_one, one_zpow, one_mul]
  apply Int.emod_nonneg
  apply NeZero.ne

-- @[cases_eliminator]
-- def cases { motive: CyclicGroup n -> Prop } := sorry

end CyclicGroup
