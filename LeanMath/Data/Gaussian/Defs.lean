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

def i := ofPoly Poly.X

def isqp1 : i ^ 2 + 1 = 0 := by
  show ofPoly _ = ofPoly _
  apply sound
  apply Rel.intro

end Gaussian
