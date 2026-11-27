module

public import Math.Algebra.Monoid.Congruence
public import Math.Algebra.Group.Defs.Hom

namespace Math

variable [RelLike C α] [IsCon C α]

public theorem resp_inv [GroupOps α] [IsGroup α] [IsMulCon C α] (r: C) (a b: α) :
  r a b -> r (a⁻¹) (b⁻¹) := by
  intro h
  rw [←mul_one (b⁻¹)]
  apply htrans (b := (b⁻¹ * (b * a⁻¹)))
  rw [←mul_assoc, inv_mul_cancel, one_mul]
  apply refl; apply resp_mul
  apply refl; apply symm
  rw [←mul_inv_cancel a]
  apply resp_mul; assumption
  apply refl

public theorem resp_neg [AddGroupOps α] [IsAddGroup α] [IsAddCon C α] (r: C) (a b: α) :
  r a b -> r (-a) (-b) :=
  resp_inv (MulOfAdd.mk r) (MulOfAdd.mk a) (MulOfAdd.mk b)

public theorem resp_powz [GroupOps α] [IsGroup α] [IsMulCon C α] (r: C) (a b: α) (n: ℤ) :
  r a b -> r (a ^ n) (b ^ n) := by
  intro h; cases n with
  | ofNat n =>
    dsimp
    rw [powz_ofNat, powz_ofNat]
    apply resp_pown
    assumption
  | negSucc =>
    rw [powz_negSucc, powz_negSucc]
    apply resp_inv
    apply resp_pown
    assumption

public theorem resp_zsmul [AddGroupOps α] [IsAddGroup α] [IsAddCon C α] (r: C) (n: ℤ) (a b: α) :
  r a b -> r (n • a) (n • b) :=
  resp_powz (MulOfAdd.mk r) (MulOfAdd.mk a) (MulOfAdd.mk b) n

public theorem resp_div [GroupOps α] [IsGroup α] [IsMulCon C α] (r: C) (a b c d: α) :
  r a c -> r b d -> r (a / b) (c / d) := by
  intro ac bd
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply resp_mul; assumption
  apply resp_inv; assumption

public theorem resp_sub [AddGroupOps α] [IsAddGroup α] [IsAddCon C α] (r: C) (a b c d: α) :
  r a c -> r b d -> r (a - b) (c - d) :=
  resp_div (MulOfAdd.mk r) (MulOfAdd.mk a) (MulOfAdd.mk b) (MulOfAdd.mk c) (MulOfAdd.mk d)

public instance [GroupOps α] [IsGroup α] [IsMulCon C α] (r: C) : Inv (AlgQuot r) where
  inv := AlgQuot.lift (fun a => AlgQuot.mk r (a⁻¹)) <| by
    intro a b h; apply AlgQuot.sound
    apply resp_inv
    assumption

public instance [GroupOps α] [IsGroup α] [IsMulCon C α] (r: C) : Pow (AlgQuot r) ℤ where
  pow q n := q.lift (fun a => AlgQuot.mk r (a ^ n)) <| by
    intro a b h; apply AlgQuot.sound
    apply resp_powz
    assumption

public instance [GroupOps α] [IsGroup α] [IsMulCon C α] (r: C) : Div (AlgQuot r) where
  div := AlgQuot.lift₂ (fun a b => AlgQuot.mk r (a / b)) <| by
    intro a b c d h g; apply AlgQuot.sound
    apply resp_div
    assumption
    assumption

public instance [AddGroupOps α] [IsAddGroup α] [IsAddCon C α] (r: C) : Neg (AlgQuot r) where
  neg := AlgQuot.lift (fun a => AlgQuot.mk r (-a)) <| by
    intro a b h; apply AlgQuot.sound
    apply resp_neg
    assumption

public instance [AddGroupOps α] [IsAddGroup α] [IsAddCon C α] : IsSMulCon C ℤ α where
  resp_smul := resp_zsmul

public instance [AddGroupOps α] [IsAddGroup α] [IsAddCon C α] (r: C) : Sub (AlgQuot r) where
  sub := AlgQuot.lift₂ (fun a b => AlgQuot.mk r (a - b)) <| by
    intro a b c d h g; apply AlgQuot.sound
    apply resp_sub
    assumption
    assumption

public instance [GroupOps α] [IsGroup α] [IsMulCon C α] (r: C) : IsGroup (AlgQuot r) where
  div_eq_mul_inv a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [div_eq_mul_inv]
  inv_mul_cancel a := by
    induction a with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [inv_mul_cancel]
  powz_ofNat a n := by
    induction a with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [powz_ofNat]
  powz_negSucc a n := by
    induction a with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [powz_negSucc]

public instance [AddGroupOps α] [IsAddGroup α] [IsAddCon C α] (r: C) : IsAddGroup (AlgQuot r) where
  sub_eq_add_neg a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [sub_eq_add_neg]
  neg_add_cancel a := by
    induction a with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [neg_add_cancel]
  ofNat_zsmul a n := by
    induction a with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [ofNat_zsmul]
  negSucc_zsmul a n := by
    induction a with | _ a =>
    show AlgQuot.mk _ _ = AlgQuot.mk _ _
    rw [negSucc_zsmul]
