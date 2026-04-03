import LeanMath.Algebra.Group.Free
import LeanMath.Data.ZMod.Defs

inductive Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (g: FreeGroup Unit) : Rel n (g ^ n) 1

-- the cyclic group of order n
def CyclicGroup (n: ℕ) := GroupQuot (Rel n)

namespace CyclicGroup

def equiv_quot : CyclicGroup n ≃ GroupQuot (Rel n) := Equiv.id _

def ι : CyclicGroup n := GroupQuot.mk _ (FreeGroup.ι ())

instance : GroupOps (CyclicGroup n) := (inferInstance: (GroupOps (GroupQuot _)))

instance : IsComm (CyclicGroup n) := (inferInstance: (IsComm (GroupQuot _)))
instance : IsGroup (CyclicGroup n) := (inferInstance: (IsGroup (GroupQuot _)))

def pown_eq_one (x: CyclicGroup n) : x ^ n = 1 := by
  induction x using GroupQuot.ind with | mk x =>
  induction x with
  | one => simp [map_one]; apply one_npow
  | inv x ih =>
    simp [map_inv]
    rw [←one_inv, ←ih]
    apply eq_inv_of_mul
    erw [←mul_npow, inv_mul_cancel, one_npow]
  | mul a b iha ihb =>
    erw [map_mul, mul_npow, iha, ihb, mul_one]
  | ι x =>
    apply GroupQuot.sound
    apply Rel.intro

def generated_by_ι (x: CyclicGroup n) : ∃k: ℤ, x = ι ^ k := by
  induction x using GroupQuot.ind with | mk x =>
  induction x with
  | one =>
    exists 0
    rw [zpow_zero, map_one]; rfl
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
    rw [zpow_add]; rfl

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

end CyclicGroup
