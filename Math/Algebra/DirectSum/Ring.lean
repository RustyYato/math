module

public import Math.Algebra.DirectSum.Defs
public import Math.Algebra.Ring.Defs.Basic
public import Math.Algebra.Group.Action.Defs.Basic

import Math.Algebra.Group.Defs.Lemmas

namespace Math

namespace DirectSum

variable
  {α: Type*} {R: α -> Type*}
  [∀a, AddGroupOps (R a)] [∀a, IsAddGroup (R a)] [∀a, IsAddComm (R a)]

public def negHom : (⊕a, R a) →+ (⊕a, R a) :=
  liftAdd fun a => {
    toFun x := ι a (-x)
    map_zero := by rw [neg_zero, map_zero]
    map_add a b := by rw [←neg_add_neg, map_add]
  }

public theorem negHom_ι (r: R a) : negHom (ι a r) = ι a (-r) := liftAdd_ι _ _ _

public instance : Neg (⊕a, R a) where
  neg a := negHom a
public instance : Sub (⊕a, R a) where
  sub a b := a + -b
public instance : SMul ℤ (⊕a, R a) := inferInstance

public instance : IsAddGroup (⊕a, R a) where
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel a := by
    show negHom a + a = 0
    induction a with
    | zero => rw [map_zero, add_zero]
    | add a b iha ihb =>
      rw [map_add, add_assoc, ←add_assoc _ a, add_comm _ a,
        add_assoc, ←add_assoc, iha, ihb, add_zero]
    | ι a r => rw [negHom_ι, ←map_add, neg_add_cancel, map_zero]
  ofNat_zsmul a n := by
    induction a with
    | zero => rw [smul_zero, smul_zero]
    | add a b iha ihb => rw [smul_add, smul_add, iha, ihb]
    | ι => rw [smul_ι, smul_ι, ofNat_zsmul]
  negSucc_zsmul a n := by
    show _ = negHom _
    induction a with
    | zero => rw [smul_zero, smul_zero, map_zero]
    | add a b iha ihb => rw [smul_add, smul_add, iha, ihb, map_add]
    | ι => rw [smul_ι, smul_ι, negHom_ι, negSucc_zsmul]

section

variable [Zero α] [IntCast (R 0)]

public instance : IntCast (⊕a, R a) where
  intCast n := ι 0 n

variable [NatCast (R 0)]

public instance [IsLawfulIntCast (R 0)] : IsLawfulIntCast (⊕a, R a) where
  intCast_ofNat n := by
    show ι (0: α) (((n: ℕ): ℤ): R 0) = _
    rw [intCast_ofNat]; rfl
  intCast_negSucc n := by
    show ι 0 ((Int.negSucc n): R 0) = negHom (ι _ _)
    rw [intCast_negSucc, negHom_ι]

public instance
  [One (R 0)] [NatCast (R 0)]
  [IsLawfulNatCast (R 0)]
  [IsLawfulIntCast (R 0)] : IsAddGroupWithOne (⊕a, R a) where

end

variable
  [Add α] [GradedMul R] [IsLawfulGradedZeroMul R]
  [IsGradedLeftDistrib R] [IsGradedRightDistrib R]
  [IsAddSemigroup α] [IsGradedSemigroup R]

public instance : IsNonUnitalRing (⊕a, R a) where

variable [Zero α] [One (R 0)]
  [NatCast (R 0)] [IsLawfulNatCast (R 0)]
  [IntCast (R 0)] [IsLawfulIntCast (R 0)]
  [IsLawfulZero α] [IsLawfulGradedOne R]

public instance : RingOps (⊕a, R a) := inferInstance
public instance : IsRing (⊕a, R a) where

end DirectSum

section
