import LeanMath.Algebra.Semigroup.Defs

class MonoidOps (α: Type*) extends One α, Mul α where
  toPowN : Pow α ℕ := by infer_instance
class AddMonoidOps (α: Type*) extends Zero α, Add α where
  toNSMul : SMul ℕ α := by infer_instance

def defaultPowN [One α] [Mul α] : Pow α ℕ where
  pow a n := n.rec 1 (fun _ acc => acc * a)
def defaultSMulN [o: Zero α] [Add α] : SMul ℕ α where
  smul n a := n.rec 0 (fun _ acc => acc + a)

section

attribute [local instance] defaultPowN defaultSMulN

def default_npow_zero [One α] [Mul α] (a: α) : a ^ 0 = 1 := rfl
def default_npow_succ [One α] [Mul α] (a: α) (n: ℕ) : a ^ (n + 1) = a ^ n * a := rfl

def default_zero_nsmul [Zero α] [Add α] (a: α) : 0 • a = 0 := rfl
def default_succ_nsmul [Zero α] [Add α] (a: α) (n: ℕ) : (n + 1) • a = n • a + a := rfl

end

instance (priority := 100) [MonoidOps α] : One α := MonoidOps.toOne
instance (priority := 100) [MonoidOps α] : Mul α := MonoidOps.toMul
instance (priority := 100) [MonoidOps α] : Pow α ℕ := MonoidOps.toPowN

instance (priority := 1100) [One α] [Mul α] [Pow α ℕ] : MonoidOps α where

instance (priority := 100) [AddMonoidOps α] : Zero α := AddMonoidOps.toZero
instance (priority := 100) [AddMonoidOps α] : Add α := AddMonoidOps.toAdd
instance (priority := 100) [AddMonoidOps α] : SMul ℕ α := AddMonoidOps.toNSMul

instance (priority := 1100) [Zero α] [Add α] [SMul ℕ α] : AddMonoidOps α where

class IsLawfulOneMul (α: Type*) [One α] [Mul α] where
  protected one_mul (a: α) : 1 * a = a
  protected mul_one (a: α) : a * 1 = a

def one_mul [One α] [Mul α] [IsLawfulOneMul α] (a: α) : 1 * a = a := IsLawfulOneMul.one_mul _
def mul_one [One α] [Mul α] [IsLawfulOneMul α] (a: α) : a * 1 = a := IsLawfulOneMul.mul_one _

class IsLawfulPowN (α: Type*) [MonoidOps α] where
  protected npow_zero (a: α) : a ^ 0 = 1 := by apply default_npow_zero
  protected npow_succ (a: α) (n: ℕ) : a ^ (n + 1) = a ^ n * a := by apply default_npow_succ

def npow_zero [MonoidOps α] [IsLawfulPowN α] (a: α) : a ^ 0 = 1 := IsLawfulPowN.npow_zero _
def npow_succ [MonoidOps α] [IsLawfulPowN α] (a: α) (n: ℕ) : a ^ (n + 1) = a ^ n * a := IsLawfulPowN.npow_succ _ _

class IsLawfulZeroAdd (α: Type*) [Zero α] [Add α] where
  protected zero_add (a: α) : 0 + a = a
  protected add_zero (a: α) : a + 0 = a

def zero_add [Zero α] [Add α] [IsLawfulZeroAdd α] (a: α) : 0 + a = a := IsLawfulZeroAdd.zero_add _
def add_zero [Zero α] [Add α] [IsLawfulZeroAdd α] (a: α) : a + 0 = a := IsLawfulZeroAdd.add_zero _

class IsLawfulNSMul (α: Type*) [AddMonoidOps α] where
  protected zero_nsmul (a: α) : 0 • a = 0 := by apply default_zero_nsmul
  protected succ_nsmul (n: ℕ) (a: α) : (n + 1) • a = n • a + a := by apply default_succ_nsmul

def zero_nsmul [AddMonoidOps α] [IsLawfulNSMul α] (a: α) : 0 • a = 0 := IsLawfulNSMul.zero_nsmul _
def succ_nsmul [AddMonoidOps α] [IsLawfulNSMul α] (n: ℕ) (a: α) : (n + 1) • a = n • a + a := IsLawfulNSMul.succ_nsmul _ _

class IsMonoid (α: Type*) [MonoidOps α] : Prop extends IsSemigroup α, IsLawfulOneMul α, IsLawfulPowN α where
class IsAddMonoid (α: Type*) [AddMonoidOps α] : Prop extends IsAddSemigroup α, IsLawfulZeroAdd α, IsLawfulNSMul α where

instance : IsMonoid ℕ where
  one_mul _ := by rw [Nat.one_mul]
  mul_one _ := by rw [Nat.mul_one]
  npow_zero _ := rfl
  npow_succ _ _ := rfl

instance : IsAddMonoid ℕ where
  zero_add _ := by rw [Nat.zero_add]
  add_zero _ := by rw [Nat.add_zero]
  zero_nsmul _ := Nat.zero_mul _
  succ_nsmul _ _ := Nat.succ_mul _ _

instance : IsMonoid ℤ where
  one_mul _ := by rw [Int.one_mul]
  mul_one _ := by rw [Int.mul_one]
  npow_zero := Int.pow_zero
  npow_succ := Int.pow_succ

instance : IsAddMonoid ℤ where
  zero_add _ := by rw [Int.zero_add]
  add_zero _ := by rw [Int.add_zero]
  zero_nsmul _ := Int.zero_mul _
  succ_nsmul n a := by
    show ((n + 1: ℕ): ℤ) * a = n * a + a
    rw [Int.natCast_succ, Int.add_mul, Int.one_mul]

section

class IsOneHom (F α β: Type*) [FunLike F α β] [One α] [One β] where
  protected map_one (f: F) : f 1 = 1 := by intro f; exact f.map_one
class IsZeroHom (F α β: Type*) [FunLike F α β] [Zero α] [Zero β] where
  protected map_zero (f: F) : f 0 = 0 := by intro f; exact f.map_zero

class IsLogOneHom (F α β: Type*) [FunLike F α β] [One α] [Zero β] where
  protected map_one_to_zero (f: F) : f 1 = 0 := by intro f; exact f.map_one_to_zero
class IsExpZeroHom (F α β: Type*) [FunLike F α β] [Zero α] [One β] where
  protected map_zero_to_one (f: F) : f 0 = 1 := by intro f; exact f.map_zero_to_one

structure OneHom (α β: Type*) [One α] [One β] extends Hom α β where
  protected map_one: toFun 1 = 1

structure ZeroHom (α β: Type*) [Zero α] [Zero β] extends Hom α β where
  protected map_zero: toFun 0 = 0

structure LogOneHom (α β: Type*) [One α] [Zero β] extends Hom α β where
  protected map_one_to_zero: toFun 1 = 0

structure ExpZeroHom (α β: Type*) [Zero α] [One β] extends Hom α β where
  protected map_zero_to_one: toFun 0 = 1

infixr:80 " →₁ " => OneHom
infixr:80 " →₀ " => ZeroHom
infixr:80 " →₁₀ " => LogOneHom
infixr:80 " →₀₁ " => ExpZeroHom

structure GroupHom (α β: Type*) [One α] [One β] [Mul α] [Mul β] extends Hom α β, α →₁ β, α →*ₙ β where
structure AddGroupHom (α β: Type*) [Zero α] [Zero β] [Add α] [Add β] extends Hom α β, α →₀ β, α →+ₙ β where
structure LogHom (α β: Type*) [One α] [Zero β] [Mul α] [Add β] extends Hom α β, α →₁₀ β, α →*+ₙ β where
structure ExpHom (α β: Type*) [Zero α] [One β] [Add α] [Mul β] extends Hom α β, α →₀₁ β, α →+*ₙ β where

infixr:80 " →* " => GroupHom
infixr:80 " →+ " => AddGroupHom
infixr:80 " →*+ " => LogHom
infixr:80 " →+* " => ExpHom

variable
  [FunLike F α β] [Zero α] [Zero β] [One α] [One β]
  [IsOneHom F α β] [IsZeroHom F α β] [IsLogOneHom F α β] [IsExpZeroHom F α β]

def map_one (f: F) : f 1 = 1 := IsOneHom.map_one f
def map_zero (f: F) : f 0 = 0 := IsZeroHom.map_zero f
def map_one_to_zero (f: F) : f 1 = 0 := IsLogOneHom.map_one_to_zero f
def map_zero_to_one (f: F) : f 0 = 1 := IsExpZeroHom.map_zero_to_one f

instance (priority := 10000) : FunLike (α →₁ β) α β where
instance (priority := 10000) : FunLike (α →₀ β) α β where
instance (priority := 10000) : FunLike (α →₀₁ β) α β where
instance (priority := 10000) : FunLike (α →₁₀ β) α β where

instance (priority := 10000) : IsOneHom (α →₁ β) α β where
instance (priority := 10000) : IsZeroHom (α →₀ β) α β where
instance (priority := 10000) : IsLogOneHom (α →₁₀ β) α β where
instance (priority := 10000) : IsExpZeroHom (α →₀₁ β) α β where

variable [Add α] [Add β] [Mul α] [Mul β]
  [IsAddHom F α β] [IsMulHom F α β] [IsLogHom F α β] [IsExpHom F α β]

instance (priority := 10000) : FunLike (α →* β) α β where
instance (priority := 10000) : FunLike (α →+ β) α β where
instance (priority := 10000) : FunLike (α →+* β) α β where
instance (priority := 10000) : FunLike (α →*+ β) α β where

instance (priority := 10000) : IsOneHom (α →* β) α β where
instance (priority := 10000) : IsZeroHom (α →+ β) α β where
instance (priority := 10000) : IsLogOneHom (α →*+ β) α β where
instance (priority := 10000) : IsExpZeroHom (α →+* β) α β where

instance (priority := 10000) : IsMulHom (α →* β) α β where
instance (priority := 10000) : IsAddHom (α →+ β) α β where
instance (priority := 10000) : IsLogHom (α →*+ β) α β where
instance (priority := 10000) : IsExpHom (α →+* β) α β where

protected def GroupHom.id (α: Type*) [One α] [Mul α] : α →* α where
  toFun := id
  map_one := rfl
  map_mul _ _ := rfl

@[simp] def GroupHom.apply_id (x: α) : GroupHom.id α x = x := rfl

@[ext] def GroupHom.ext (f g: α →* β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h
@[ext] def AddGroupHom.ext (f g: α →+ β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h
@[ext] def LogHom.ext (f g: α →*+ β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h
@[ext] def ExpHom.ext (f g: α →+* β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h

def AddOfMul.mkHom : α →*+ AddOfMul α where
  toFun := mk
  map_one_to_zero := rfl
  map_mul_to_add _ _ := rfl

def AddOfMul.getHom : AddOfMul α →+* α where
  toFun := get
  map_zero_to_one := rfl
  map_add_to_mul _ _ := rfl

def MulOfAdd.mkHom : α →+* MulOfAdd α where
  toFun := mk
  map_zero_to_one := rfl
  map_add_to_mul _ _ := rfl

def MulOfAdd.getHom : MulOfAdd α →*+ α where
  toFun := get
  map_one_to_zero := rfl
  map_mul_to_add _ _ := rfl

@[induction_eliminator]
def AddOfMul.indHom {motive: AddOfMul α -> Prop} (mk: ∀a, motive (.mkHom a)) (a: AddOfMul α) : motive a := mk a.get
@[induction_eliminator]
def MulOfAdd.indHom {motive: MulOfAdd α -> Prop} (mk: ∀a, motive (.mkHom a)) (a: MulOfAdd α) : motive a := mk a.get

def AddOfMul.mk_get_hom (a: α) : getHom (mkHom a) = a := rfl
def AddOfMul.get_mk_hom (a: AddOfMul α) : mkHom (getHom a) = a := rfl
def MulOfAdd.mk_get_hom (a: α) : getHom (mkHom a) = a := rfl
def MulOfAdd.get_mk_hom (a: MulOfAdd α) : mkHom (getHom a) = a := rfl

variable [Pow α ℕ] [Pow β ℕ] [SMul ℕ α] [SMul ℕ β]

instance [IsLawfulZeroAdd α] : IsLawfulOneMul (MulOfAdd α) where
  one_mul a := by
    induction a with | mk a =>
    show MulOfAdd.mkHom (0 + a) = _
    rw [zero_add]
  mul_one a := by
    induction a with | mk a =>
    show MulOfAdd.mkHom (a + 0) = _
    rw [add_zero]

instance [IsLawfulOneMul α] : IsLawfulZeroAdd (AddOfMul α) where
  zero_add a := by
    induction a with | mk a =>
    show AddOfMul.mkHom (1 * a) = _
    rw [one_mul]
  add_zero a := by
    induction a with | mk a =>
    show AddOfMul.mkHom (a * 1) = _
    rw [mul_one]

instance [IsLawfulNSMul α] : IsLawfulPowN (MulOfAdd α) where
  npow_zero a := by
    induction a with | mk a =>
    show (MulOfAdd.mkHom (0 • a)) = 1
    rw [zero_nsmul]
    rfl
  npow_succ a n := by
    induction a with | mk a =>
    show (MulOfAdd.mkHom ((n + 1) • a)) = MulOfAdd.mkHom (n • a + a)
    rw [succ_nsmul]

instance [IsLawfulPowN α] : IsLawfulNSMul (AddOfMul α) where
  zero_nsmul a := by
    induction a with | mk a =>
    show (AddOfMul.mkHom (a ^ 0)) = 0
    rw [npow_zero]
    rfl
  succ_nsmul n a := by
    induction a with | mk a =>
    show (AddOfMul.mkHom (a ^ (n + 1))) = AddOfMul.mkHom (a ^ n * a)
    rw [npow_succ]

def map_group_hom_to_add_group_hom (f: F) : AddOfMul α →+ AddOfMul β where
  toFun a := .mk (f a.get)
  map_zero := map_one f
  map_add := map_mul f

def map_add_group_hom_to_group_hom (f: F) : MulOfAdd α →* MulOfAdd β where
  toFun a := .mk (f a.get)
  map_one := map_zero f
  map_mul := map_add f

def map_npow [IsLawfulPowN α] [IsLawfulPowN β] (f: F) (a: α) (n: ℕ) : f (a ^ n) = (f a) ^ n := by
  induction n with
  | zero => rw [npow_zero, npow_zero, map_one]
  | succ n ih => rw [npow_succ, npow_succ, map_mul, ih]

def map_nsmul [IsLawfulNSMul α] [IsLawfulNSMul β] (f: F) (a: α) (n: ℕ) : f (n • a) = n • f a :=
  map_npow (map_add_group_hom_to_group_hom f) _ _

end

section

variable [Zero α] [Add α] [SMul ℕ α] [One α] [Mul α] [Pow α ℕ]

instance [IsLawfulZeroAdd α] : IsLawfulOneMul (MulOfAdd α) where
  one_mul := zero_add (α := α)
  mul_one := add_zero (α := α)
instance [IsLawfulOneMul α] : IsLawfulZeroAdd (AddOfMul α) where
  zero_add := one_mul (α := α)
  add_zero := mul_one (α := α)

instance [IsLawfulNSMul α] : IsLawfulPowN (MulOfAdd α) where
  npow_zero := zero_nsmul (α := α)
  npow_succ _ _ := succ_nsmul (α := α) _ _
instance [IsLawfulPowN α] : IsLawfulNSMul (AddOfMul α) where
  zero_nsmul := npow_zero (α := α)
  succ_nsmul _ _ := npow_succ (α := α) _ _

instance [IsAddMonoid α] : IsMonoid (MulOfAdd α) where
instance [IsMonoid α] : IsAddMonoid (AddOfMul α) where

variable [IsMonoid α] [IsAddMonoid α]

instance (a b: α) (n: ℕ) [IsCommAt a b] : IsCommAt (a ^ n) b where
  mul_comm := by
    induction n with
    | zero => rw [npow_zero, one_mul, mul_one]
    | succ n ih => rw [npow_succ, mul_assoc, mul_comm a b, ←mul_assoc, ih, mul_assoc]

instance (a b: α) (n: ℕ) [IsCommAt a b] : IsCommAt b (a ^ n) where
  mul_comm := by
    symm
    rw [mul_comm]

instance (a b: α) (n: ℕ) [IsAddCommAt a b] : IsAddCommAt (n • a) b where
  add_comm := mul_comm (MulOfAdd.mkHomₙ a ^ n) (MulOfAdd.mkHomₙ b)

instance (a b: α) (n: ℕ) [IsAddCommAt a b] : IsAddCommAt b (n • a) where
  add_comm := mul_comm (MulOfAdd.mkHomₙ b) (MulOfAdd.mkHomₙ a ^ n)

def one_npow (n: ℕ) : (1: α) ^ n = 1 := by
    induction n with
    | zero => rw [npow_zero]
    | succ n ih => rw [npow_succ, mul_one, ih]

def mul_npow (a b: α) (n: ℕ) [IsCommAt a b] : (a * b) ^ n = a ^ n * b ^ n := by
    induction n with
    | zero => rw [npow_zero, npow_zero, npow_zero, mul_one]
    | succ n ih =>
      rw [npow_succ, npow_succ, ih]
      rw [mul_assoc _ a, mul_comm a (b ^ _), npow_succ, mul_assoc, mul_assoc,
        mul_comm b]

def nsmul_zero (n: ℕ) : n • (0: α) = 0 :=
  one_npow (α := MulOfAdd α) _

def nsmul_add (a b: α) (n: ℕ) [IsAddCommAt a b] : n • (a + b) = n • a + n • b :=
  mul_npow (α := MulOfAdd α) (MulOfAdd.mkHomₙ a) (MulOfAdd.mkHomₙ b) n

instance (a b: α) (m n: ℕ) [IsCommAt a b] : IsCommAt (a ^ m) (b ^ n) := inferInstance

instance (a b: α) (m n: ℕ) [IsAddCommAt a b] : IsAddCommAt (m • a) (n • b) := inferInstance

def npowHom [IsComm α] (n: ℕ) : α →* α where
  toFun a := a ^ n
  map_one := by rw [one_npow]
  map_mul a b := by rw [mul_npow]

def npowAtHom (a: α) : ℕ →+* α where
  toFun n := a ^ n
  map_zero_to_one := by rw [npow_zero]
  map_add_to_mul n m := by
    induction m with
    | zero => rw [add_zero, npow_zero, mul_one]
    | succ m ih => rw [Nat.add_succ, npow_succ, npow_succ, ←mul_assoc, ih]

def nsmulHom [IsAddComm α] (n: ℕ) : α →+ α where
  toFun a := n • a
  map_zero := by rw [nsmul_zero]
  map_add a b := by rw [nsmul_add]

def nsmulAtHom (a: α) : ℕ →+ α where
  toFun n := n • a
  map_zero := by rw [zero_nsmul]
  map_add n m := by
    induction m with
    | zero => rw [add_zero, zero_nsmul, add_zero]
    | succ m ih => rw [Nat.add_succ, succ_nsmul, succ_nsmul, ←add_assoc, ih]

def npow_eq_npowAtHom (a: α) (n: ℕ) : a ^ n = npowAtHom a n := rfl
def nsmul_eq_nsmulAtHom (a: α) (n: ℕ) : n • a = nsmulAtHom a n := rfl

end
