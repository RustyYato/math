import LeanMath.Algebra.Group.Free
import LeanMath.Data.ZMod.Group

inductive Rel (n: ℕ) : FreeGroup Unit -> FreeGroup Unit -> Prop where
| intro (g: FreeGroup Unit) : Rel n (g ^ n) 1

-- the cyclic group of order n
structure CyclicGroup (n: ℕ) where
  ofQuot :: toQuot : GroupQuot (Rel n)

namespace CyclicGroup

private abbrev equiv_quot₀ : CyclicGroup n ≃ GroupQuot (Rel n) where
  toFun := CyclicGroup.toQuot
  invFun := CyclicGroup.ofQuot
  leftInv _ := rfl
  rightInv _ := rfl

instance : One (CyclicGroup n) := ⟨equiv_quot₀.symm 1⟩
instance : Mul (CyclicGroup n) where
  mul a b := equiv_quot₀.symm (equiv_quot₀ a * equiv_quot₀ b)
instance : Div (CyclicGroup n) where
  div a b := equiv_quot₀.symm (equiv_quot₀ a / equiv_quot₀ b)
instance : Inv (CyclicGroup n) where
  inv a := equiv_quot₀.symm (equiv_quot₀ a)⁻¹
instance : Pow (CyclicGroup n) ℕ where
  pow a n := equiv_quot₀.symm <| (equiv_quot₀ a) ^ n
instance : Pow (CyclicGroup n) ℤ where
  pow a n := equiv_quot₀.symm <| (equiv_quot₀ a) ^ n


def equiv_quot : CyclicGroup n ≃* GroupQuot (Rel n) where
  toFun := CyclicGroup.toQuot
  invFun := CyclicGroup.ofQuot
  leftInv _ := rfl
  rightInv _ := rfl
  map_one := rfl
  map_mul _ _ := rfl

instance : IsLawfulDiv (CyclicGroup n) :=
  IsLawfulDiv.lift equiv_quot (fun _ => rfl) (fun _ _ => rfl)
instance : IsLawfulPowN (CyclicGroup n) :=
  IsLawfulPowN.lift equiv_quot (fun _ _ => rfl)
instance : IsLawfulPowZ (CyclicGroup n) :=
  IsLawfulPowZ.lift equiv_quot (fun _ => rfl) (fun _ _ => rfl)
instance : IsGroup (CyclicGroup n) :=
  IsGroup.lift equiv_quot (fun _ => rfl)
instance : IsComm (CyclicGroup n) :=
  IsComm.lift equiv_quot

def ofFree : FreeGroup Unit →* CyclicGroup n :=
  equiv_quot.symm.toGroupHom.comp (GroupQuot.mk _)

def ι : CyclicGroup n := equiv_quot.symm (GroupQuot.mk _ (FreeGroup.ι ()))

def preind
  {motive: CyclicGroup n -> Prop}
  (ofFree: ∀x: FreeGroup Unit, motive (ofFree x))
  (x: CyclicGroup n) : motive x := by
  obtain ⟨x⟩ := x
  induction x using GroupQuot.ind with | mk x =>
  apply ofFree

def generated_by_ι
  (x: CyclicGroup n) : ∃n: ℤ, x = ι ^ n := by
  cases x using preind with | _ x =>
  induction x with
  | one =>
    exists 0
    rw [map_one, zpow_zero]
  | mul a b ha hb =>
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exists a + b
    rw [map_mul, ha, hb, zpow_add]
  | inv a ha =>
    obtain ⟨a, ha⟩ := ha
    exists -a
    rw [map_inv, ha, zpow_neg]
  | ι =>
    exists 1; rw [zpow_one]; rfl

def pown_eq_one (x: CyclicGroup n) : x ^ n = 1 := by
  cases x using preind with | _ x =>
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
    show equiv_quot.symm (_) ^ n = _
    rw [←map_npow, ←map_one equiv_quot.symm]
    congr; apply GroupQuot.sound
    apply Rel.intro

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

def lift [GroupOps α] [IsGroup α]
  (h: ∀x: α, x ^ n = 1) (x: α) : CyclicGroup n →* α :=
  (GroupQuot.lift (Rel n) {
    val := FreeGroup.lift (fun _ => x)
    property := by
      intro x y h
      cases h
      rw [map_npow, map_one]; apply h
  }).comp equiv_quot.toGroupHom

def lift_ι [GroupOps α] [IsGroup α] (h: ∀x: α, x ^ n = 1) : lift h x ι = x := by
  unfold lift ι
  simp [FreeGroup.lift_ι]

def pow : CyclicGroup n ≃* MulOfAdd (ZMod n) where
  toFun := lift (by
    intro x
    cases x using MulOfAdd.induction with | mk x =>
    show MulOfAdd.mkHom x ^ n = 1
    show MulOfAdd.mkHom (n • x) = 1
    rw [ZMod.nsmul_eq_natCast_mul, ZMod.natCast_degree, zero_mul]
    rfl) (MulOfAdd.mkHom 1)
  invFun x := ι ^ x.get.val
  leftInv x := by
    cases x using MulOfAdd.induction with | mk x =>
    dsimp; rw [map_zpow, lift_ι]
    show MulOfAdd.mkHom (x.val • 1) = MulOfAdd.mkHom x
    congr; apply mul_one
  rightInv x := by
    obtain ⟨x, rfl⟩ := generated_by_ι x
    dsimp; rw [map_zpow, lift_ι]
    show ι ^ (x • (1: ZMod n)).val = ι ^ x
    rw [ZMod.zsmul_val, ZMod.one_val]
    rw [Int.mul_emod, Int.emod_emod, ←Int.mul_emod]
    rw [mul_one]; rw (occs := [2]) [←Int.emod_add_ediv_mul x n]
    rw [zpow_add, zpow_mul, zpow_ofNat, pown_eq_one, mul_one]
  map_one := map_one _
  map_mul := map_mul _

end CyclicGroup
