import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.Int.Defs

class GroupOps (α: Type*) extends MonoidOps α, Inv α, Div α where
  toPowZ : Pow α ℤ := by infer_instance

class AddGroupOps (α: Type*) extends AddMonoidOps α, Neg α, Sub α where
  toZSMul : SMul ℤ α := by infer_instance

instance (priority := 100) [GroupOps α] : One α := inferInstance
instance (priority := 100) [GroupOps α] : Mul α := inferInstance
instance (priority := 100) [GroupOps α] : Pow α ℕ := inferInstance
instance (priority := 100) [GroupOps α] : Inv α := inferInstance
instance (priority := 100) [GroupOps α] : Div α := inferInstance
instance (priority := 100) [GroupOps α] : Pow α ℤ := GroupOps.toPowZ
instance (priority := 100) [GroupOps α] : MonoidOps α := inferInstance

instance (priority := 1100) [One α] [Mul α] [Pow α ℕ] [Inv α] [Div α] [Pow α ℤ] : GroupOps α where

instance (priority := 100) [AddGroupOps α] : Zero α := inferInstance
instance (priority := 100) [AddGroupOps α] : Add α := inferInstance
instance (priority := 100) [AddGroupOps α] : SMul ℕ α := inferInstance
instance (priority := 100) [AddGroupOps α] : Neg α := inferInstance
instance (priority := 100) [AddGroupOps α] : Sub α := inferInstance
instance (priority := 100) [AddGroupOps α] : SMul ℤ α := AddGroupOps.toZSMul
instance (priority := 100) [AddGroupOps α] : AddMonoidOps α := inferInstance

instance (priority := 1100) [Zero α] [Add α] [SMul ℕ α] [Neg α] [Sub α] [SMul ℤ α] : AddGroupOps α where

class IsLawfulDiv (α: Type*) [Mul α] [Inv α] [Div α] where
  protected div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
class IsLawfulSub (α: Type*) [Add α] [Neg α] [Sub α] where
  protected sub_eq_add_neg (a b: α) : a - b = a + -b

def div_eq_mul_inv [Mul α] [Inv α] [Div α] [IsLawfulDiv α] (a b: α) : a / b = a * b⁻¹ := IsLawfulDiv.div_eq_mul_inv _ _
def sub_eq_add_neg [Add α] [Neg α] [Sub α] [IsLawfulSub α] (a b: α) : a - b = a + -b := IsLawfulSub.sub_eq_add_neg _ _

class IsLawfulPowZ (α: Type*) [GroupOps α] : Prop extends IsLawfulPowN α where
  protected zpow_ofNat (a: α) (n: ℕ) : a ^ (n: ℤ) = a ^ n
  protected zpow_negSucc (a: α) (n: ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹

def zpow_ofNat [GroupOps α] [IsLawfulPowZ α] (a: α) (n: ℕ) : a ^ (n: ℤ) = a ^ n := IsLawfulPowZ.zpow_ofNat _ _
def zpow_negSucc [GroupOps α] [IsLawfulPowZ α] (a: α) (n: ℕ) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := IsLawfulPowZ.zpow_negSucc _ _

class IsLawfulZSMul (α: Type*) [AddGroupOps α] : Prop extends IsLawfulNSMul α where
  protected ofNat_zsmul (a: α) (n: ℕ) : (n: ℤ) • a = n • a
  protected negSucc_zsmul (a: α) (n: ℕ) : (Int.negSucc n) • a = -((n + 1) • a)

def ofNat_zsmul [AddGroupOps α] [IsLawfulZSMul α] (a: α) (n: ℕ) : (n: ℤ) • a = n • a := IsLawfulZSMul.ofNat_zsmul _ _
def negSucc_zsmul [AddGroupOps α] [IsLawfulZSMul α] (a: α) (n: ℕ) : (Int.negSucc n) • a = -((n + 1) • a) := IsLawfulZSMul.negSucc_zsmul _ _

class IsGroup (α: Type*) [GroupOps α] : Prop extends IsMonoid α, IsLawfulDiv α, IsLawfulPowZ α where
  protected mul_inv_cancel (a: α) : a * a⁻¹ = 1

class IsAddGroup (α: Type*) [AddGroupOps α] : Prop extends IsAddMonoid α, IsLawfulSub α, IsLawfulZSMul α where
  protected add_neg_cancel (a: α) : a + -a = 0

def mul_inv_cancel [GroupOps α] [IsGroup α] (a: α) : a * a⁻¹ = 1 := IsGroup.mul_inv_cancel _
def add_neg_cancel [AddGroupOps α] [IsAddGroup α] (a: α) : a + -a = 0 := IsAddGroup.add_neg_cancel _

instance : IsAddGroup ℤ where
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  add_neg_cancel _ := Int.sub_eq_zero.mpr rfl
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul a b := by
    show Int.negSucc b * a = -((b + 1: ℕ) * a)
    rw [←Int.neg_mul, Int.neg_ofNat_succ b]

instance [Add α] [Neg α] [Sub α] [IsLawfulSub α] : IsLawfulDiv (MulOfAdd α) where
  div_eq_mul_inv := sub_eq_add_neg (α := α)
instance [Mul α] [Inv α] [Div α] [IsLawfulDiv α] : IsLawfulSub (AddOfMul α) where
  sub_eq_add_neg := div_eq_mul_inv (α := α)

instance [GroupOps α] [IsLawfulPowZ α] : IsLawfulZSMul (AddOfMul α) where
  ofNat_zsmul := zpow_ofNat (α := α)
  negSucc_zsmul := zpow_negSucc (α := α)

instance [AddGroupOps α] [IsLawfulZSMul α] : IsLawfulPowZ (MulOfAdd α) where
  zpow_ofNat := ofNat_zsmul (α := α)
  zpow_negSucc := negSucc_zsmul (α := α)

instance [GroupOps α] [IsLawfulPowZ α] : IsLawfulZSMul (AddOfMul α) where
  ofNat_zsmul := zpow_ofNat (α := α)
  negSucc_zsmul := zpow_negSucc (α := α)

instance [AddGroupOps α] [IsAddGroup α] : IsGroup (MulOfAdd α) where
  mul_inv_cancel := add_neg_cancel (α := α)

instance [GroupOps α] [IsGroup α] : IsAddGroup (AddOfMul α) where
  add_neg_cancel := mul_inv_cancel (α := α)

section

variable [FunLike F α β] [GroupOps α] [GroupOps β] [IsGroup α] [IsGroup β]
  [IsMulHom F α β] [IsOneHom F α β]
  [AddGroupOps α] [AddGroupOps β] [IsAddGroup α] [IsAddGroup β]
  [IsAddHom F α β] [IsZeroHom F α β]

def eq_inv_of_mul (a b: α) (h: a * b = 1) : a = b⁻¹ := by
  rw [←one_mul (b⁻¹), ←h, mul_assoc, mul_inv_cancel, mul_one]

def eq_neg_of_add (a b: α) (h: a + b = 0) : a = -b :=
  eq_inv_of_mul (α := MulOfAdd α) _ _ h

def inv_mul_cancel (a: α) : a⁻¹ * a = 1 := by
  rw (occs := [2]) [←mul_one a]
  rw (occs := [1]) [←mul_inv_cancel (a⁻¹)]
  rw [←mul_assoc a, mul_inv_cancel, one_mul, mul_inv_cancel]

def neg_add_cancel (a: α) : -a + a = 0 :=
  inv_mul_cancel (α := MulOfAdd α) _

def map_inv (f: F) (x: α) : f (x⁻¹) = (f x)⁻¹ := by
  apply eq_inv_of_mul
  rw [←map_mul, inv_mul_cancel, map_one]

def map_div (f: F) (a b: α) : f (a / b) = f a / f b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_inv]

def map_zpow (f: F) (a: α) (z: ℤ) : f (a ^ z) = f a ^ z := by
  cases z <;> rename_i z
  rw [zpow_ofNat, zpow_ofNat, map_npow]
  rw [zpow_negSucc, zpow_negSucc, map_inv, map_npow]

def map_neg (f: F) (x: α) : f (-x) = -f x :=
  map_inv (map_add_group_hom_to_group_hom f) _

def map_sub (f: F) (a b: α) : f (a - b) = f a - f b :=
  map_div (map_add_group_hom_to_group_hom f) _ _

def map_zsmul (f: F) (a: α) (z: ℤ) : f (z • a) = z • f a :=
  map_zpow (map_add_group_hom_to_group_hom f) _ _

end

section

variable [RelLike R α] [Mul α] [Inv α] [One α] [IsMulCon R] [Add α] [Neg α] [Zero α] [IsAddCon R]
  (r: R)

end

section

variable [RelLike R α] [GroupOps α] [IsGroup α] [IsMulCon R]
  (r: R)

def resp_inv (r: R) (a b: α) : r a b -> r a⁻¹ b⁻¹ := by
  intro h
  have raa : r a⁻¹ a⁻¹ := (IsCon.eqv _).refl _
  have rbb : r b⁻¹ b⁻¹ := (IsCon.eqv _).refl _
  have := resp_mul r (resp_mul r raa h) rbb
  rw [inv_mul_cancel a, mul_assoc, mul_inv_cancel, mul_one, one_mul] at this
  apply (IsCon.eqv _).symm
  assumption

def resp_div (r: R) (a b c d: α) : r a c -> r b d -> r (a / b) (c / d) := by
  intro h g
  rw [div_eq_mul_inv, div_eq_mul_inv]
  apply resp_mul
  assumption
  apply resp_inv
  assumption

def resp_zpow (r: R) (z: ℤ) (a b: α) : r a b  -> r (a ^ z) (b ^ z) := by
  intro h
  cases z <;> rename_i z
  rw [zpow_ofNat, zpow_ofNat]
  apply resp_npow
  assumption
  rw [zpow_negSucc, zpow_negSucc]
  apply resp_inv
  apply resp_npow
  assumption

instance: Inv (AlgQuot r) where
  inv := by
    refine Quotient.lift ?_ ?_
    exact fun a => AlgQuot.mk r (a⁻¹)
    intros
    apply AlgQuot.sound
    apply resp_inv
    assumption

instance: Div (AlgQuot r) where
  div := by
    refine Quotient.lift₂ ?_ ?_
    exact fun a b => AlgQuot.mk r (a / b)
    intros
    apply AlgQuot.sound
    apply resp_div
    assumption
    assumption

instance : IsPowCon R ℤ where
  resp_pow := by
    intros; apply resp_zpow
    assumption

instance : IsGroup (AlgQuot r) where
  div_eq_mul_inv a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    show (AlgQuot.mk r (a / b)) = (AlgQuot.mk r (a * b⁻¹))
    rw [div_eq_mul_inv]
  zpow_ofNat a n := by
    induction a with | mk a =>
    show (AlgQuot.mk r (a ^ (n: ℤ))) = (AlgQuot.mk r (a ^ n))
    rw [zpow_ofNat]
  zpow_negSucc a n := by
    induction a with | mk a =>
    show (AlgQuot.mk r (a ^ (Int.negSucc n))) = (AlgQuot.mk r ((a ^ (n + 1: ℕ))⁻¹))
    rw [zpow_negSucc]
  mul_inv_cancel a := by
    induction a with | mk a =>
    show (AlgQuot.mk r (a * a⁻¹)) = 1
    rw [mul_inv_cancel, map_one]

end
section

variable [RelLike R α] [AddGroupOps α] [IsAddGroup α] [IsAddCon R]
  (r: R)

def resp_neg (r: R) (a b: α) : r a b -> r (-a) (-b) := by
  intro h
  have raa : r (-a) (-a) := (IsCon.eqv _).refl _
  have rbb : r (-b) (-b) := (IsCon.eqv _).refl _
  have := resp_add r (resp_add r raa h) rbb
  rw [neg_add_cancel a, add_assoc, add_neg_cancel, add_zero, zero_add] at this
  apply (IsCon.eqv _).symm
  assumption

def resp_sub (r: R) (a b c d: α) : r a c -> r b d -> r (a - b) (c - d) := by
  intro h g
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply resp_add
  assumption
  apply resp_neg
  assumption

def resp_zsmul (r: R) (z: ℤ) (a b: α) : r a b  -> r (z • a) (z • b) := by
  intro h
  cases z <;> rename_i z
  rw [ofNat_zsmul, ofNat_zsmul]
  apply resp_nsmul
  assumption
  rw [negSucc_zsmul, negSucc_zsmul]
  apply resp_neg
  apply resp_nsmul
  assumption

instance: Neg (AlgQuot r) where
  neg := by
    refine Quotient.lift ?_ ?_
    exact fun a => AlgQuot.mk r (-a)
    intros
    apply AlgQuot.sound
    apply resp_neg
    assumption

instance: Sub (AlgQuot r) where
  sub := by
    refine Quotient.lift₂ ?_ ?_
    exact fun a b => AlgQuot.mk r (a - b)
    intros
    apply AlgQuot.sound
    apply resp_sub
    assumption
    assumption

instance : IsSMulCon R ℤ where
  resp_smul := by
    intros; apply resp_zsmul
    assumption

instance : IsAddGroup (AlgQuot r) where
  sub_eq_add_neg a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    show (AlgQuot.mk r (a - b)) = (AlgQuot.mk r (a + -b))
    rw [sub_eq_add_neg]
  ofNat_zsmul a n := by
    induction a with | mk a =>
    show (AlgQuot.mk r ((n: ℤ) • a)) = (AlgQuot.mk r (n • a))
    rw [ofNat_zsmul]
  negSucc_zsmul a n := by
    induction a with | mk a =>
    show (AlgQuot.mk r ((Int.negSucc n) • a)) = (AlgQuot.mk r (-((n + 1: ℕ) • a)))
    rw [negSucc_zsmul]
  add_neg_cancel a := by
    induction a with | mk a =>
    show (AlgQuot.mk r (a + -a)) = 0
    rw [add_neg_cancel, map_zero]

end
