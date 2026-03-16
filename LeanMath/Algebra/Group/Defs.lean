import LeanMath.Algebra.Monoid.Defs
import LeanMath.Data.Int.Defs

class GroupOps (α: Type*) extends MonoidOps α, Inv α, Div α where
  toPowZ : Pow α ℤ := by infer_instance

class AddGroupOps (α: Type*) extends AddMonoidOps α, Neg α, Sub α where
  toZSMul : SMul ℤ α := by infer_instance

def defaultPowZ [Pow α ℕ] [Inv α] : Pow α ℤ where
  pow
  | a, .ofNat n => a ^ n
  | a, .negSucc n => (a ^ (n + 1))⁻¹
def defaultSMulZ [SMul ℕ α] [Neg α] : SMul ℤ α where
  smul
  | .ofNat n, a => n • a
  | .negSucc n, a => -((n + 1) • a)

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

class IsLawfulInvRight (α: Type*) [Mul α] [Inv α] [One α] where
  protected mul_inv_cancel (a: α) : a * a⁻¹ = 1

class IsLawfulInvLeft (α: Type*) [Mul α] [Inv α] [One α] where
  protected inv_mul_cancel (a: α) : a⁻¹ * a = 1

class IsLawfulNegRight (α: Type*) [Add α] [Neg α] [Zero α] where
  protected add_neg_cancel (a: α) : a + -a = 0

class IsLawfulNegLeft (α: Type*) [Add α] [Neg α] [Zero α] where
  protected neg_add_cancel (a: α) : -a + a = 0

def inv_mul_cancel [Mul α] [Inv α] [One α] [IsLawfulInvLeft α] (a: α) : a⁻¹ * a = 1 :=
  IsLawfulInvLeft.inv_mul_cancel _
def mul_inv_cancel [Mul α] [Inv α] [One α] [IsLawfulInvRight α] (a: α) : a * a⁻¹ = 1 :=
  IsLawfulInvRight.mul_inv_cancel _

def add_neg_cancel [Add α] [Neg α] [Zero α] [IsLawfulNegRight α] (a: α) : a + -a = 0 :=
  IsLawfulNegRight.add_neg_cancel _
def neg_add_cancel [Add α] [Neg α] [Zero α] [IsLawfulNegLeft α] (a: α) : -a + a = 0 :=
  IsLawfulNegLeft.neg_add_cancel _

instance [Mul α] [Inv α] [One α] [IsLawfulInvLeft α] : IsLawfulInvRight αᵐᵒᵖ where
  mul_inv_cancel := inv_mul_cancel (α := α)
instance [Mul α] [Inv α] [One α] [IsLawfulInvRight α] : IsLawfulInvLeft αᵐᵒᵖ where
  inv_mul_cancel := mul_inv_cancel (α := α)

instance [Mul α] [Inv α] [One α] [IsLawfulInvLeft α] : IsLawfulNegLeft (AddOfMul α) where
  neg_add_cancel := inv_mul_cancel (α := α)
instance [Mul α] [Inv α] [One α] [IsLawfulInvRight α] : IsLawfulNegRight (AddOfMul α) where
  add_neg_cancel := mul_inv_cancel (α := α)

instance [Add α] [Neg α] [Zero α] [IsLawfulNegLeft α] : IsLawfulInvLeft (MulOfAdd α) where
  inv_mul_cancel := neg_add_cancel (α := α)
instance [Add α] [Neg α] [Zero α] [IsLawfulNegRight α] : IsLawfulInvRight (MulOfAdd α) where
  mul_inv_cancel := add_neg_cancel (α := α)

instance [Mul α] [Inv α] [One α] [IsSemigroup α] [IsLawfulOneMul α] [IsLawfulInvLeft α] : IsLawfulInvRight α where
  mul_inv_cancel a := by
    rw (occs := [1]) [←one_mul a, ←inv_mul_cancel (a⁻¹)]
    rw [mul_assoc (a⁻¹⁻¹), inv_mul_cancel, mul_one, inv_mul_cancel]

instance [Mul α] [Inv α] [One α] [IsSemigroup α] [IsLawfulOneMul α] [IsLawfulInvRight α] : IsLawfulInvLeft α where
  inv_mul_cancel := mul_inv_cancel (α := αᵐᵒᵖ)

instance [Add α] [Neg α] [Zero α] [IsAddSemigroup α] [IsLawfulZeroAdd α] [IsLawfulNegLeft α] : IsLawfulNegRight α where
  add_neg_cancel := add_neg_cancel (α := AddOfMul (MulOfAdd α))
instance [Add α] [Neg α] [Zero α] [IsAddSemigroup α] [IsLawfulZeroAdd α] [IsLawfulNegRight α] : IsLawfulNegLeft α where
  neg_add_cancel := inv_mul_cancel (α := MulOfAdd α)

class IsLawfulDiv (α: Type*) [Mul α] [Inv α] [Div α] where
  protected div_eq_mul_inv (a b: α) : a / b = a * b⁻¹
class IsLawfulSub (α: Type*) [Add α] [Neg α] [Sub α] where
  protected sub_eq_add_neg (a b: α) : a - b = a + -b

def div_eq_mul_inv [Mul α] [Inv α] [Div α] [IsLawfulDiv α] (a b: α) : a / b = a * b⁻¹ := IsLawfulDiv.div_eq_mul_inv _ _
def sub_eq_add_neg [Add α] [Neg α] [Sub α] [IsLawfulSub α] (a b: α) : a - b = a + -b := IsLawfulSub.sub_eq_add_neg _ _

class IsLawfulOneInv (α: Type*) [Inv α] [One α] : Prop where
  protected one_inv : (1: α)⁻¹ = 1

class IsLawfulNegZero (α: Type*) [Neg α] [Zero α] : Prop where
  protected neg_zero : -(0: α) = 0

def one_inv [Inv α] [One α] [IsLawfulOneInv α] : (1: α)⁻¹ = 1 := IsLawfulOneInv.one_inv
def neg_zero [Neg α] [Zero α] [IsLawfulNegZero α] : -(0: α) = 0 := IsLawfulNegZero.neg_zero

instance [Inv α] [One α] [IsLawfulOneInv α] : IsLawfulNegZero (AddOfMul α) where
  neg_zero := one_inv (α := α)
instance [Neg α] [Zero α] [IsLawfulNegZero α] : IsLawfulOneInv (MulOfAdd α) where
  one_inv := neg_zero (α := α)

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

class IsGroup (α: Type*) [GroupOps α] : Prop extends IsMonoid α, IsLawfulDiv α, IsLawfulPowZ α, IsLawfulInvRight α where

class IsAddGroup (α: Type*) [AddGroupOps α] : Prop extends IsAddMonoid α, IsLawfulSub α, IsLawfulZSMul α, IsLawfulNegRight α where

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

def div_self (a: α) : a / a = 1 := by
  rw [div_eq_mul_inv, mul_inv_cancel]

def sub_self (a: α) : a - a = 0 :=
  div_self (α := MulOfAdd α) _

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

section

variable [GroupOps α] [IsGroup α]

instance : IsLeftCancel α where
  of_mul_left {k a b} h := by
    rw [←one_mul a, ←one_mul b, ←inv_mul_cancel k,
      mul_assoc, mul_assoc, h]

instance : IsRightCancel α where
  of_mul_right {k a b} h := by
    rw [←mul_one a, ←mul_one b, ←mul_inv_cancel k,
      ←mul_assoc, ←mul_assoc, h]

instance (a b: α) [IsCommAt a b] : IsCommAt a⁻¹ b where
  mul_comm := by
    apply of_mul_left (k := a)
    rw [←mul_assoc, ←mul_assoc, mul_inv_cancel, one_mul,
      mul_comm a, mul_assoc, mul_inv_cancel, mul_one]

instance (a b: α) [IsCommAt a b] : IsCommAt b a⁻¹ := inferInstance

def inv_mul_rev (a b: α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  symm; apply eq_inv_of_mul
  rw [mul_assoc, ←mul_assoc _ a, inv_mul_cancel, one_mul, inv_mul_cancel]

def inv_inv (a: α) : a⁻¹⁻¹ = a := by
  symm; apply eq_inv_of_mul
  rw [mul_inv_cancel]

def inv_inj {a b: α} : a⁻¹ = b⁻¹ ↔ a = b := by
  apply Iff.intro
  · intro h
    rw [←inv_inv a, ←inv_inv b, h]
  · intro h
    congr

def inv_div (a b: α) : (a / b)⁻¹ = b / a := by
  rw [div_eq_mul_inv, div_eq_mul_inv, inv_mul_rev, inv_inv]

instance : IsLawfulOneInv α where
  one_inv := by
    symm; apply eq_inv_of_mul
    rw [mul_one]

def mul_div_assoc (a b c: α) : (a * b) / c = a * (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

def div_mul (a b c: α) : a / (b * c) = a / c / b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    inv_mul_rev, mul_assoc]

def mul_div_comm (a b c: α) [IsCommAt b c] : a * c / b = a / b * c := by
  rw [div_eq_mul_inv, div_eq_mul_inv,
    mul_assoc, mul_assoc, mul_comm _ c]

def div_one (a: α) : a / 1 = a := by
  rw [div_eq_mul_inv, one_inv, mul_one]

def one_zpow (z: ℤ) : (1: α) ^ z = 1 := by
  cases z
  rw [zpow_ofNat, one_npow]
  rw [zpow_negSucc, one_npow, one_inv]

def mul_zpow (a b: α) (z: ℤ) [IsCommAt a b] : (a * b) ^ z = a ^ z * b ^ z := by
  cases z
  iterate 3 rw [zpow_ofNat]
  rw [mul_npow]
  iterate 3 rw [zpow_negSucc]
  rw [mul_npow, mul_comm, inv_mul_rev]

def zpowHom [IsComm α] (z: ℤ) : α →* α where
  toFun a := a ^ z
  map_one := by rw [one_zpow]
  map_mul a b := by rw [mul_zpow]

def zpow_zero (a: α) : a ^ (0: ℤ) = 1 := by
  rw [←npow_zero a, ←zpow_ofNat a 0]
  rfl

def zpow_neg_one (a: α) : a ^ (-1) = a⁻¹ := by
  erw [zpow_negSucc a 0]
  rw [npow_succ, npow_zero, one_mul]

instance (a b: α) [IsCommAt a b] : IsCommAt (a⁻¹) b where
  mul_comm := by
    rw (occs := [2]) [←inv_inv b]
    rw [←inv_mul_rev]
    apply eq_inv_of_mul
    rw [mul_assoc, ←mul_assoc _ a, ←mul_comm a, mul_assoc,
      mul_inv_cancel, mul_one, inv_mul_cancel]

instance (a b: α) [IsCommAt a b] : IsCommAt b (a⁻¹) where
  mul_comm := by symm; rw [mul_comm]

def inv_zpow (a: α) (n: ℤ) : a⁻¹ ^ n = a ^ (-n) := by
  cases n <;> rename_i n
  rw [zpow_ofNat]
  cases n
  rw [npow_zero, Int.ofNat_zero, Int.neg_zero, zpow_zero]
  erw [←Int.negSucc_eq]
  rw [zpow_negSucc]
  apply eq_inv_of_mul
  rw [←mul_npow, inv_mul_cancel, one_npow]
  rw [zpow_negSucc, Int.neg_negSucc, zpow_ofNat]
  symm; apply eq_inv_of_mul
  rw [←mul_npow, mul_inv_cancel, one_npow]

def zpow_succ (a: α) (n: ℤ) : a ^ (n + 1) = a ^ n * a := by
  cases n
  erw [Int.ofNat_add_ofNat]; rw [zpow_ofNat, zpow_ofNat, npow_succ]
  rename_i n
  cases n
  simp; rw [zpow_zero, zpow_neg_one]
  rw [inv_mul_cancel]
  erw [Int.negSucc_add_ofNat, zpow_negSucc, zpow_negSucc]
  rename_i n
  symm; apply eq_inv_of_mul
  rw [mul_assoc, mul_comm a, ←npow_succ, inv_mul_cancel]

def zpow_pred (a: α) (n: ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ := by
  have := zpow_succ (a⁻¹) (-n)
  repeat rw [inv_zpow] at this
  rwa [Int.neg_neg, Int.neg_add, Int.neg_neg, ←sub_eq_add_neg] at this

def zpow_add (a: α) (n m: ℤ) : a ^ (n + m) = a ^ n * a ^ m := by
  induction m using Int.succ_pred_induction with
  | zero => rw [add_zero, zpow_zero, mul_one]
  | succ m ih => rw [←add_assoc, zpow_succ, zpow_succ, ih, mul_assoc]
  | pred m ih => rw [←Int.add_sub_assoc, zpow_pred, zpow_pred, ih, mul_assoc]

def zpow_sub (a: α) (n m: ℤ) : a ^ (n - m) = a ^ n / a ^ m := by
  rw [div_eq_mul_inv, sub_eq_add_neg, zpow_add]
  congr
  apply eq_inv_of_mul
  rw [←zpow_add, neg_add_cancel, zpow_zero]

def zpow_one (a: α) : a ^ (1: ℤ) = a := by
  show (a ^ (0 + 1: ℤ)) = a
  rw [zpow_succ, zpow_zero, one_mul]

def zpowAtHom (a: α) : ℤ →ₐ* α where
  toFun z := a ^ z
  map_zero_to_one := by rw [zpow_zero]
  map_add_to_mul n m := by rw [zpow_add]

def zpow_mul (a: α) (n m: ℤ) : a ^ (n * m) = (a ^ n) ^ m := by
  induction m using Int.succ_pred_induction with
  | zero => rw [Int.mul_zero, zpow_zero, zpow_zero]
  | succ m ih => rw [Int.mul_add, mul_one, zpow_add, zpow_succ, ih]
  | pred m ih => rw [Int.mul_sub, mul_one, zpow_sub, zpow_pred, ih, div_eq_mul_inv]

def zpow_neg (a: α) (n: ℤ) : a ^ (-n) = (a ^ n)⁻¹ := by
  apply eq_inv_of_mul
  rw [←zpow_add, neg_add_cancel, zpow_zero]

def div_eq_one_of_eq (a b: α) : a = b -> a / b = 1 := by
  intro rfl; rw [div_self]

def div_eq_one (a b: α) : a = b ↔ a / b = 1:= by
  apply Iff.intro
  apply div_eq_one_of_eq
  intro h
  rw [←one_mul b, ←h, div_eq_mul_inv a b,
    mul_assoc, inv_mul_cancel, mul_one]

end

section

variable [AddGroupOps α] [IsAddGroup α]

instance : IsLeftAddCancel α where
  of_add_left := of_mul_left (α := MulOfAdd α)

instance : IsRightAddCancel α where
  of_add_right := of_mul_right (α := MulOfAdd α)

instance (a b: α) [IsAddCommAt a b] : IsAddCommAt (-a) b where
  add_comm := mul_comm (MulOfAdd.mkHomₙ a)⁻¹ (MulOfAdd.mkHomₙ b)

instance (a b: α) [IsAddCommAt a b] : IsAddCommAt b (-a) := inferInstance

def neg_add_rev (a b: α) : -(a + b) = -b + -a :=
  inv_mul_rev (α := MulOfAdd α) _ _

def neg_neg (a: α) : - -a = a :=
  inv_inv (α := MulOfAdd α) _

def neg_inj {a b: α} : -a = -b ↔ a = b :=
  inv_inj (α := MulOfAdd α)

def neg_sub (a b: α) : -(a - b) = b - a :=
  inv_div (α := MulOfAdd α) _ _

instance : IsLawfulNegZero α where
  neg_zero := one_inv (α := MulOfAdd α)

def add_sub_assoc (a b c: α) : (a + b) - c = a + (b - c) :=
  mul_div_assoc (α := MulOfAdd α) _ _ _

def sub_add (a b c: α) : a - (b + c) = a - c - b :=
    div_mul (α := MulOfAdd α) _ _ _

def add_sub_comm (a b c: α) [IsAddCommAt b c] : a + c - b = a - b + c :=
  mul_div_comm (α := MulOfAdd α) (MulOfAdd.mkHomₙ a) (MulOfAdd.mkHomₙ b) (MulOfAdd.mkHomₙ c)

def sub_zero (a: α) : a - 0 = a :=
  div_one (α := MulOfAdd α) _

def zsmul_zero (z: ℤ) : z • (0: α) = 0 :=
  one_zpow (α := MulOfAdd α) _

def zsmul_add (a b: α) (z: ℤ) [IsAddCommAt a b] : z • (a + b) = z • a + z • b :=
  mul_zpow (α := MulOfAdd α) (MulOfAdd.mkHomₙ _) (MulOfAdd.mkHomₙ _) _

def zsmulHom [IsAddComm α] (z: ℤ) : α →+ α where
  toFun a := z • a
  map_zero := by rw [zsmul_zero]
  map_add a b := by rw [zsmul_add]

def zero_zsmul (a: α) : (0: ℤ) • a = 0 :=
  zpow_zero (α := MulOfAdd α) _

def neg_one_zsmul (a: α) : (-1) • a = -a :=
  zpow_neg_one (α := MulOfAdd α) _

instance (a b: α) [IsAddCommAt a b] : IsAddCommAt (-a) b where
  add_comm :=
    mul_comm (α := MulOfAdd α) (MulOfAdd.mkHomₙ a)⁻¹ (MulOfAdd.mkHomₙ b)

instance (a b: α) [IsAddCommAt a b] : IsAddCommAt b (-a) where
  add_comm := by symm; rw [add_comm]

def zsmul_neg (a: α) (n: ℤ) : n • -a = (-n) • a :=
  inv_zpow (α := MulOfAdd α) _ _

def succ_zsmul (a: α) (n: ℤ) : (n + 1) • a = n • a + a :=
  zpow_succ (α := MulOfAdd α) _ _

def pred_zsmul (a: α) (n: ℤ) : (n - 1) • a = n • a + -a :=
  zpow_pred (α := MulOfAdd α) _ _

def add_zsmul (a: α) (n m: ℤ) : (n + m) • a = n • a + m • a :=
  zpow_add (α := MulOfAdd α) _ _ _

def sub_zsmul (a: α) (n m: ℤ) : (n - m) • a = n • a - m • a :=
  zpow_sub (α := MulOfAdd α) _ _ _

def one_zsmul (a: α) : (1: ℤ) • a = a :=
  zpow_one (α := MulOfAdd α) _

def zsmulAtHom (a: α) : ℤ →+ α where
  toFun z := z • a
  map_zero := by rw [zero_zsmul]
  map_add n m := by rw [add_zsmul]

def mul_zsmul (a: α) (n m: ℤ) : (n * m) • a = m • n • a :=
  zpow_mul (α := MulOfAdd α) _ _ _

def neg_zsmul (a: α) (n: ℤ) : (-n) • a = -(n • a) :=
  zpow_neg (α := MulOfAdd α) _ _

def sub_eq_zero_of_eq (a b: α) : a = b -> a - b = 0 := by
  intro rfl; rw [sub_self]

def sub_eq_zero (a b: α) : a = b ↔ a - b = 0 :=
  div_eq_one (α := MulOfAdd α) _ _

def negHom [IsAddComm α] : α →+ α where
  toFun a := -a
  map_zero := by rw [neg_zero]
  map_add a b := by rw [add_comm, neg_add_rev]

@[simp] def apply_negHom [IsAddComm α] (a: α) : negHom a = -a := rfl

end

def IsGroup.lift
  [GroupOps α] [IsLawfulPowN α] [IsLawfulPowZ α] [IsLawfulDiv α]
  [GroupOps β] [IsGroup β]
  [EmbeddingLike F α β] [IsMulHom F α β] [IsOneHom F α β]
  (f: F) (hinv: ∀a, f (a⁻¹) = (f a)⁻¹) : IsGroup α := {
    IsMonoid.lift f, inferInstanceAs (IsLawfulPowZ α) with
    mul_inv_cancel a := by
      apply inj f
      rw [map_mul, hinv, mul_inv_cancel, map_one]
  }

def IsAddGroup.lift
  [AddGroupOps α] [IsLawfulNSMul α] [IsLawfulZSMul α] [IsLawfulSub α]
  [AddGroupOps β] [IsAddGroup β]
  [EmbeddingLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (hneg: ∀a, f (-a) = -f a) : IsAddGroup α := {
    IsAddMonoid.lift f, inferInstanceAs (IsLawfulZSMul α) with
    add_neg_cancel a := by
      apply inj f
      rw [map_add, hneg, add_neg_cancel, map_zero]
  }

namespace Units

instance [MonoidOps α] [IsMonoid α] : Pow (Units α) ℤ := defaultPowZ
instance [MonoidOps α] [IsMonoid α] : Div (Units α) where
  div a b := a * b⁻¹

instance [MonoidOps α] [IsMonoid α] : IsLawfulPowZ (Units α) where
  zpow_ofNat _ _ := rfl
  zpow_negSucc _ _ := rfl
instance [MonoidOps α] [IsMonoid α] : IsLawfulDiv (Units α) where
  div_eq_mul_inv _ _ := rfl

instance [MonoidOps α] [IsMonoid α] : IsGroup (Units α) where
  mul_inv_cancel a := by
    apply inj Units.get
    apply a.val_mul_inv

def Units.equiv {α: Type*} [GroupOps α] [IsGroup α] : α ≃* Units α :=
  GroupEquiv.symm {
    toFun := Units.get
    invFun a := {
      val := a
      inv := a⁻¹
      val_mul_inv := mul_inv_cancel _
      inv_mul_val := inv_mul_cancel _
    }
    leftInv _ := rfl
    rightInv _ := inj get rfl
    map_one := rfl
    map_mul _ _ := rfl
  }

instance [GroupOps α] [IsGroup α] (a: α) : IsUnit a where
  exists_eq_unit := ⟨Units.equiv a, rfl⟩

end Units

namespace AddUnits

instance [AddMonoidOps α] [IsAddMonoid α] : SMul ℤ (AddUnits α) := defaultSMulZ
instance [AddMonoidOps α] [IsAddMonoid α] : Sub (AddUnits α) where
  sub a b := a + -b

instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulZSMul (AddUnits α) where
  ofNat_zsmul _ _ := rfl
  negSucc_zsmul _ _ := rfl
instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulSub (AddUnits α) where
  sub_eq_add_neg _ _ := rfl

instance [AddMonoidOps α] [IsAddMonoid α] : IsAddGroup (AddUnits α) where
  add_neg_cancel a := by
    apply inj AddUnits.get
    apply a.val_add_neg

def AddUnits.equiv {α: Type*} [AddGroupOps α] [IsAddGroup α] : α ≃+ AddUnits α :=
  AddGroupEquiv.symm {
    toFun := AddUnits.get
    invFun a := {
      val := a
      neg := -a
      val_add_neg := add_neg_cancel _
      neg_add_val := neg_add_cancel _
    }
    leftInv _ := rfl
    rightInv _ := inj get rfl
    map_zero := rfl
    map_add _ _ := rfl
  }

instance [AddGroupOps α] [IsAddGroup α] (a: α) : IsAddUnit a where
  exists_eq_add_unit := ⟨AddUnits.equiv a, rfl⟩

end AddUnits
