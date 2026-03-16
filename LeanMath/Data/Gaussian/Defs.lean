import LeanMath.Data.Poly.Ring

open Poly in
inductive Gaussian.Rel : ℤ[X] -> ℤ[X] -> Prop where
| intro : Rel (X ^ 2 + 1) 0

open Poly in
def Gaussian.Con := RingCon.generate Gaussian.Rel

structure Gaussian where
  ofQuot :: toQuot : AlgQuot Gaussian.Con

namespace Gaussian

instance : NatCast Gaussian where
  natCast n := ⟨n⟩
instance : IntCast Gaussian where
  intCast n := ⟨n⟩
instance : Zero Gaussian where
  zero := ⟨0⟩
instance : One Gaussian where
  one := ⟨1⟩
instance : Add Gaussian where
  add a b := ⟨a.toQuot + b.toQuot⟩
instance : Mul Gaussian where
  mul a b := ⟨a.toQuot * b.toQuot⟩
instance : SMul ℕ Gaussian where
  smul n a := ⟨n • a.toQuot⟩
instance : SMul ℤ Gaussian where
  smul n a := ⟨n • a.toQuot⟩
instance : Pow Gaussian ℕ where
  pow a n := ⟨a.toQuot ^ n⟩
instance : Neg Gaussian where
  neg a := ⟨-a.toQuot⟩
instance : Sub Gaussian where
  sub a b := ⟨a.toQuot - b.toQuot⟩

private def equivQuot : Gaussian ≃+* AlgQuot Gaussian.Con where
  toFun := Gaussian.toQuot
  invFun := Gaussian.ofQuot
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

instance : IsLawfulSub (AlgQuot Gaussian.Con) :=
  @IsAddGroup.toIsLawfulSub (AlgQuot Gaussian.Con) inferInstance inferInstance

instance : IsLawfulIntCast (AlgQuot Gaussian.Con) :=
  @IsAddGroupWithOne.toIsLawfulIntCast (AlgQuot Gaussian.Con) inferInstance inferInstance
instance : IsLawfulNatCast (AlgQuot Gaussian.Con) :=
  @IsAddMonoidWithOne.toIsLawfulNatCast (AlgQuot Gaussian.Con) inferInstance inferInstance

instance : IsLawfulPowN Gaussian :=
  IsLawfulPowN.lift equivQuot (fun _ _ => rfl)
instance : IsLawfulSub Gaussian where
  sub_eq_add_neg _ _ := by
    apply inj equivQuot
    show equivQuot _ - equivQuot _ = equivQuot _ + -equivQuot _
    apply sub_eq_add_neg
instance : IsLawfulNSMul Gaussian :=
  IsLawfulNSMul.lift equivQuot (fun _ _ => rfl)
instance : IsLawfulZSMul Gaussian where
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul a n := by
    apply inj equivQuot
    show Int.negSucc _ • equivQuot _ = _
    apply Eq.trans
    apply negSucc_zsmul (equivQuot a) n
    rfl

instance : IsAddGroup Gaussian :=
  IsAddGroup.lift equivQuot (fun _ => rfl)
instance : IsMonoid Gaussian := IsMonoid.lift equivQuot
instance : IsAddComm Gaussian := IsAddComm.lift equivQuot
instance : IsComm Gaussian := IsComm.lift equivQuot
instance : IsLeftDistrib Gaussian where
  mul_add _ _ _ := by
    apply inj equivQuot
    apply mul_add
instance : IsLawfulZeroMul Gaussian where
  mul_zero _ := by apply inj equivQuot; apply mul_zero
  zero_mul _ := by apply inj equivQuot; apply zero_mul
instance : IsLawfulNatCast Gaussian where
  natCast_zero := by apply inj equivQuot; apply natCast_zero
  natCast_one := by apply inj equivQuot; apply natCast_one
  natCast_succ _ := by apply inj equivQuot; apply natCast_succ
instance : IsLawfulIntCast Gaussian where
  intCast_ofNat _ := by apply inj equivQuot; apply intCast_ofNat
  intCast_negSucc n := by apply inj equivQuot; show Int.cast _ = -equivQuot (Nat.cast (n + 1)); apply intCast_negSucc

instance : RingOps Gaussian := inferInstance
instance : IsRing Gaussian where
instance (priority := 100) : OfNat Gaussian n := ⟨n⟩

def ofPoly : ℤ[X] →+* Gaussian :=
  equivQuot.symm.toRingHom.comp {
    toFun := AlgQuot.mk Gaussian.Con
    map_zero := map_zero _
    map_one := map_one _
    map_add := map_add _
    map_mul := map_mul _
  }

def sound (a b: ℤ[X]) : Rel a b -> ofPoly a = ofPoly b := by
  intro h
  show Gaussian.ofQuot (AlgQuot.mk Gaussian.Con _) = Gaussian.ofQuot (AlgQuot.mk Gaussian.Con _)
  rw [AlgQuot.sound]
  apply RingCon.generate_of
  assumption

def ind {motive: Gaussian -> Prop} (ofPoly: ∀x, motive (ofPoly x)) (z: Gaussian) : motive z := by
  obtain ⟨z⟩ := z
  induction z with | _ z =>
  apply ofPoly

def i := ofPoly Poly.X

instance : AlgebraMap ℤ Gaussian where
  toAlgebraMap := ofPoly.comp Poly.C.toRingHom

instance : IsAlgebra ℤ Gaussian where
  smul_def r a := by
    induction a using ind with | _ a =>
    show ofPoly (r • a) = ofPoly (algebraMap ℤ r * a)
    rw [smul_def]
  commutes _ _ := mul_comm _ _

def isqp1 : i ^ 2 + 1 = 0 := by
  show ofPoly _ = ofPoly _
  apply sound
  apply Rel.intro

def isq : i ^ 2 = -1 := by
  rw [←zero_add (-1), ←isqp1, add_assoc,
    add_neg_cancel, add_zero]

def isq' : i * i = -1 := by
  rw [←isq, npow_succ, npow_one]

def basis (z: Gaussian) : ∃a b: ℤ, z = algebraMap ℤ a + b • i := by
  induction z using ind with | _ z =>
  induction z with
  | add a b iha ihb =>
    obtain ⟨a₀, b₀, h₀⟩ := iha
    obtain ⟨a₁, b₁, h₁⟩ := ihb
    exists (a₀ + a₁)
    exists (b₀ + b₁)
    rw [map_add, map_add, add_smul, h₀, h₁]
    ac_rfl
  | term p n =>
    rw [Poly.term_def, ←Poly.C_mul_eq_smul]
    induction n with
    | zero =>
      simp [npow_zero]
      exists p; exists 0
      rw [zero_smul, add_zero]
      rw [mul_one]; rfl
    | succ n ih =>
      obtain ⟨a, b, h⟩ := ih
      simp [npow_succ]
      exists -b; exists a
      rw [←mul_assoc, map_mul, h,
        add_mul, ←i, smul_def, mul_assoc,
        isq', ←neg_mul_right, mul_one, add_comm, smul_def,
        map_neg]

def neg_i_inv_i : i * -i = 1 := by
  rw [←neg_mul_right, isq', neg_neg]

private def preGetC (n: ℕ) : ℤ →+ ℤ :=
  match Fin.ofNat 4 n with
  | ⟨0, _⟩ => AddGroupHom.id _
  | ⟨1, _⟩ | ⟨3, _⟩ => 0
  | ⟨2, _⟩ => negHom

private def preGetC_congr_mul (a b c d: ℤ[X]) (ac: Con a c) (bd: Con b d)
  : Poly.liftAdd preGetC (a * b) = Poly.liftAdd preGetC (c * d) := by
  have base_case (b: ℤ[X]) : Poly.liftAdd preGetC ((Poly.X ^ 2 + 1: ℤ[X]) * b) = 0 := by
    induction b with
    | add a b iha ihb => rw [mul_add, map_add, iha, ihb, add_zero]
    | term p n =>
      rw [←one_smul (R := ℤ) (Poly.X^2), ←Poly.term_def,
        add_mul, one_mul, Poly.term_mul_term, map_add,
          Poly.liftAdd_term, Poly.liftAdd_term, one_mul]
      dsimp [preGetC]
      simp [Fin.ofNat]
      rw [add_comm]
      split <;> rename_i h <;> replace h := Fin.mk.inj h
      simp [show (2 + n) % 4 = 2 by
        rw [Nat.add_mod, h]]
      apply add_neg_cancel
      simp [show (2 + n) % 4 = 3 by
        rw [Nat.add_mod, h]]
      apply add_zero
      simp [show (2 + n) % 4 = 1 by
        rw [Nat.add_mod, h]]
      apply add_zero
      simp [show (2 + n) % 4 = 0 by
        rw [Nat.add_mod, h]]
      apply neg_add_cancel
  induction ac generalizing b d with
  | mul a' b' c' d' _ _ iha ihb =>
    rw [mul_assoc, mul_assoc]
    rw [iha _ _ (by
        apply resp_mul
        assumption
        assumption)]
  | add _ _ _ _ _ _ iha ihb =>
    simp [add_mul, map_add]
    congr 1
    apply iha
    assumption
    apply ihb
    assumption
  | symm x y h ih =>
    rw [ih]
    apply Relation.symm
    assumption
  | trans _ _ _ _ _ iha ihb =>
    rw [iha _ _ (Relation.refl _)]
    apply ihb
    assumption
  | of x y h =>
    cases h; rw [zero_mul, map_zero]
    apply base_case
  | refl =>
  rename_i x
  induction bd generalizing x with
  | mul a' b' c' d' _ _ iha ihb =>
    rw [←mul_assoc, ←mul_assoc]
    rw [←ihb, mul_assoc, mul_comm a', ←mul_assoc,
      iha, mul_assoc, mul_comm b', mul_assoc]
  | add _ _ _ _ _ _ iha ihb =>
    simp [mul_add, map_add]
    congr 1
    apply iha
    apply ihb
  | symm x y h ih => rw [ih]
  | trans _ _ _ _ _ iha ihb => rw [iha, ihb]
  | of x y h =>
    cases h; rw [mul_zero, map_zero, mul_comm]
    apply base_case
  | refl =>
    rename_i x
    rfl

def getC : Gaussian →+ ℤ :=
  AlgQuot.liftAddGroupHom {
    val := Poly.liftAdd preGetC
    property a b h := by
      induction h with
      | refl => rfl
      | symm => symm; assumption
      | trans a b _ _ _ iha ihb => rw [iha, ihb]
      | add => rw [map_add, map_add]; congr
      | of a b h =>
        cases h
        rw [map_add, ←one_smul (R := ℤ) (Poly.X ^ 2),
          ←Poly.term_def, Poly.liftAdd_term]
        rfl
      | mul a b c d ac bd iha ihb =>
        apply preGetC_congr_mul
        assumption
        assumption
  } |>.comp equivQuot.toAddGroupHom

def getI : Gaussian →+ ℤ :=
  getC.comp {
    toFun a := a * -i
    map_zero := by rw [zero_mul]
    map_add a b := by rw [add_mul]
  }

@[simp] def getC_algebraMap (c: ℤ) : getC (algebraMap ℤ c) = c := by
  apply Poly.liftAdd_term
@[simp] def getC_i : getC i = 0 := rfl

@[simp] def getI_i : getI i = 1 := rfl
@[simp] def getI_algebraMap : getI (algebraMap ℤ a) = 0 := by
  simp [getI]
  rw [←neg_mul_right, ←smul_def, map_neg, map_smul]
  simp [smul_zero]

def decompose (z: Gaussian) : z = getC z + getI z * i := by
  obtain ⟨a, b, rfl⟩ := basis z
  simp [map_add, map_smul, smul_eq_mul, mul_one, mul_zero]
  rw [smul_def]; rfl

end Gaussian
