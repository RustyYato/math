module

public import Math.Algebra.Monoid.Units
public import Math.Algebra.Group.Defs.Basic

namespace Math

public instance [Mul α] [One α] : Inv (Unit α) where
  inv a := {
    val := a.inv
    inv := a.val
    val_mul_inv := a.inv_mul_val
    inv_mul_val := a.val_mul_inv
  }

public instance [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] : Div (Unit α) where
  div a b := a * b⁻¹
public instance [MonoidOps α] [IsMonoid α] : Pow (Unit α) ℤ where
  pow a n := match n with
    | .ofNat n => a ^ n
    | .negSucc n => (a ^ (n + 1))⁻¹

public instance [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] : IsLawfulDiv (Unit α) where
  div_eq_mul_inv _ _ := rfl
public instance [MonoidOps α] [IsMonoid α] : IsGroup (Unit α) where
  powz_ofNat _ _ := rfl
  powz_negSucc _ _ := rfl
  inv_mul_cancel a := by
    ext
    apply a.inv_mul_val

public instance [Add α] [Zero α] : Neg (AddUnit α) where
  neg a := {
    val := a.neg
    neg := a.val
    val_add_neg := a.neg_add_val
    neg_add_val := a.val_add_neg
  }

public instance [Add α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α] : Sub (AddUnit α) where
  sub a b := a + -b
public instance [AddMonoidOps α] [IsAddMonoid α] : SMul ℤ (AddUnit α) where
  smul n a := match n with
    | .ofNat n => n • a
    | .negSucc n => -((n + 1) • a)

public instance [Add α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α] : IsLawfulSub (AddUnit α) where
  sub_eq_add_neg _ _ := rfl
public instance [AddMonoidOps α] [IsAddMonoid α] : IsAddGroup (AddUnit α) where
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul _ _ := rfl
  neg_add_cancel a := by
    ext
    apply a.neg_add_val
