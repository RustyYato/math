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

class IsLawfulZeroMul (α: Type*) [Zero α] [Mul α] where
  protected zero_mul (a: α) : 0 * a = 0
  protected mul_zero (a: α) : a * 0 = 0

def zero_mul [Zero α] [Mul α] [IsLawfulZeroMul α] (a: α) : 0 * a = 0 := IsLawfulZeroMul.zero_mul _
def mul_zero [Zero α] [Mul α] [IsLawfulZeroMul α] (a: α) : a * 0 = 0 := IsLawfulZeroMul.mul_zero _

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

class NoZeroDivisors (α: Type*) [Mul α] [Zero α] where
  of_mul_eq_zero {a b: α} (h: a * b = 0) : a = 0 ∨ b = 0

def of_mul_eq_zero [Mul α] [Zero α] [NoZeroDivisors α] {a b: α} (h: a * b = 0) : a = 0 ∨ b = 0 :=
  NoZeroDivisors.of_mul_eq_zero h

class IsZeroNeOne (α: Type*) [Zero α] [One α] : Prop where
  protected zero_ne_one : (0: α) ≠ (1: α)

def zero_ne_one (α: Type*) [Zero α] [One α] [IsZeroNeOne α] : (0: α) ≠ (1: α) := IsZeroNeOne.zero_ne_one

instance [Nontrivial α] [DecidableEq α] [Zero α] [One α] [Mul α]
  [IsLawfulOneMul α] [IsLawfulZeroMul α] : IsZeroNeOne α where
  zero_ne_one := by
    intro h
    have ⟨b, g⟩ := Nontrivial.exists_ne (1: α)
    rw [←mul_one b, ←h, mul_zero] at g
    contradiction

instance [Zero α] [One α] [IsZeroNeOne α] : Nontrivial α := .intro 0 1 (zero_ne_one α)

macro_rules
| `(tactic|contradiction) => `(tactic|nomatch zero_ne_one _ (by assumption))
macro_rules
| `(tactic|contradiction) => `(tactic|nomatch zero_ne_one _ (Eq.symm (by assumption)))

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

instance : IsLawfulZeroMul ℕ where
  mul_zero := Nat.mul_zero
  zero_mul := Nat.zero_mul

instance : IsLawfulZeroMul ℤ where
  mul_zero := Int.mul_zero
  zero_mul := Int.zero_mul

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

structure OneEmbedding (α β: Type*) [One α] [One β] extends α ↪ β, OneHom α β where
structure ZeroEmbedding (α β: Type*) [Zero α] [Zero β] extends α ↪ β, ZeroHom α β where
structure LogOneEmbedding (α β: Type*) [One α] [Zero β] extends α ↪ β, LogOneHom α β where
structure ExpZeroEmbedding (α β: Type*) [Zero α] [One β] extends α ↪ β, ExpZeroHom α β where

structure OneEquiv (α β: Type*) [One α] [One β] extends α ≃ β, OneHom α β where
structure ZeroEquiv (α β: Type*) [Zero α] [Zero β] extends α ≃ β, ZeroHom α β where
structure LogOneEquiv (α β: Type*) [One α] [Zero β] extends α ≃ β, LogOneHom α β where
structure ExpZeroEquiv (α β: Type*) [Zero α] [One β] extends α ≃ β, ExpZeroHom α β where

infixr:80 " →₁ " => OneHom
infixr:80 " →₀ " => ZeroHom
infixr:80 " →₁₀ " => LogOneHom
infixr:80 " →₀₁ " => ExpZeroHom

infixr:80 " ↪₁ " => OneEmbedding
infixr:80 " ↪₀ " => ZeroEmbedding
infixr:80 " ↪₁₀ " => LogOneEmbedding
infixr:80 " ↪₀₁ " => ExpZeroEmbedding

infixr:80 " ≃₁ " => OneEquiv
infixr:80 " ≃₀ " => ZeroEquiv
infixr:80 " ≃₁₀ " => LogOneEquiv
infixr:80 " ≃₀₁ " => ExpZeroEquiv

structure GroupHom (α β: Type*) [One α] [One β] [Mul α] [Mul β] extends Hom α β, α →₁ β, α →*ₙ β where
structure AddGroupHom (α β: Type*) [Zero α] [Zero β] [Add α] [Add β] extends Hom α β, α →₀ β, α →+ₙ β where
structure LogHom (α β: Type*) [One α] [Zero β] [Mul α] [Add β] extends Hom α β, α →₁₀ β, α →ₘ+ₙ β where
structure ExpHom (α β: Type*) [Zero α] [One β] [Add α] [Mul β] extends Hom α β, α →₀₁ β, α →ₐ*ₙ β where

structure GroupEmbedding (α β: Type*) [One α] [One β] [Mul α] [Mul β] extends α ↪ β, α ↪₁ β, α ↪*ₙ β where
structure AddGroupEmbedding (α β: Type*) [Zero α] [Zero β] [Add α] [Add β] extends α ↪ β, α ↪₀ β, α ↪+ₙ β where
structure LogEmbedding (α β: Type*) [One α] [Zero β] [Mul α] [Add β] extends α ↪ β, α ↪₁₀ β, α ↪ₘ+ₙ β where
structure ExpEmbedding (α β: Type*) [Zero α] [One β] [Add α] [Mul β] extends α ↪ β, α ↪₀₁ β, α ↪ₐ*ₙ β where

structure GroupEquiv (α β: Type*) [One α] [One β] [Mul α] [Mul β] extends α ≃ β, α ≃₁ β, α ≃*ₙ β where
structure AddGroupEquiv (α β: Type*) [Zero α] [Zero β] [Add α] [Add β] extends α ≃ β, α ≃₀ β, α ≃+ₙ β where
structure LogEquiv (α β: Type*) [One α] [Zero β] [Mul α] [Add β] extends α ≃ β, α ≃₁₀ β, α ≃ₘ+ₙ β where
structure ExpEquiv (α β: Type*) [Zero α] [One β] [Add α] [Mul β] extends α ≃ β, α ≃₀₁ β, α ≃ₐ*ₙ β where

infixr:80 " →* " => GroupHom
infixr:80 " →+ " => AddGroupHom
infixr:80 " →ₘ+ " => LogHom
infixr:80 " →ₐ* " => ExpHom

infixr:80 " ↪* " => GroupEmbedding
infixr:80 " ↪+ " => AddGroupEmbedding
infixr:80 " ↪ₘ+ " => LogEmbedding
infixr:80 " ↪ₐ* " => ExpEmbedding

infixr:80 " ≃* " => GroupEquiv
infixr:80 " ≃+ " => AddGroupEquiv
infixr:80 " ≃ₘ+ " => LogEquiv
infixr:80 " ≃ₐ* " => ExpEquiv

variable
  [FunLike F α β] [Zero α] [Zero β] [Zero γ] [One α] [One β] [One γ]
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

instance (priority := 10000) : EmbeddingLike (α ↪₁ β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪₀ β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪₀₁ β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪₁₀ β) α β where

instance (priority := 10000) : IsOneHom (α ↪₁ β) α β where
instance (priority := 10000) : IsZeroHom (α ↪₀ β) α β where
instance (priority := 10000) : IsLogOneHom (α ↪₁₀ β) α β where
instance (priority := 10000) : IsExpZeroHom (α ↪₀₁ β) α β where

instance (priority := 10000) : EquivLike (α ≃₁ β) α β where
instance (priority := 10000) : EquivLike (α ≃₀ β) α β where
instance (priority := 10000) : EquivLike (α ≃₀₁ β) α β where
instance (priority := 10000) : EquivLike (α ≃₁₀ β) α β where

instance (priority := 10000) : IsOneHom (α ≃₁ β) α β where
instance (priority := 10000) : IsZeroHom (α ≃₀ β) α β where
instance (priority := 10000) : IsLogOneHom (α ≃₁₀ β) α β where
instance (priority := 10000) : IsExpZeroHom (α ≃₀₁ β) α β where

variable [Add α] [Add β] [Add γ] [Mul α] [Mul β] [Mul γ]
  [IsAddHom F α β] [IsMulHom F α β] [IsLogHom F α β] [IsExpHom F α β]

instance (priority := 10000) : FunLike (α →* β) α β where
instance (priority := 10000) : FunLike (α →+ β) α β where
instance (priority := 10000) : FunLike (α →ₐ* β) α β where
instance (priority := 10000) : FunLike (α →ₘ+ β) α β where

instance (priority := 10000) : IsOneHom (α →* β) α β where
instance (priority := 10000) : IsZeroHom (α →+ β) α β where
instance (priority := 10000) : IsLogOneHom (α →ₘ+ β) α β where
instance (priority := 10000) : IsExpZeroHom (α →ₐ* β) α β where

instance (priority := 10000) : IsMulHom (α →* β) α β where
instance (priority := 10000) : IsAddHom (α →+ β) α β where
instance (priority := 10000) : IsLogHom (α →ₘ+ β) α β where
instance (priority := 10000) : IsExpHom (α →ₐ* β) α β where

instance (priority := 10000) : EmbeddingLike (α ↪* β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪+ β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪ₐ* β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪ₘ+ β) α β where

instance (priority := 10000) : IsOneHom (α ↪* β) α β where
instance (priority := 10000) : IsZeroHom (α ↪+ β) α β where
instance (priority := 10000) : IsLogOneHom (α ↪ₘ+ β) α β where
instance (priority := 10000) : IsExpZeroHom (α ↪ₐ* β) α β where

instance (priority := 10000) : IsMulHom (α ↪* β) α β where
instance (priority := 10000) : IsAddHom (α ↪+ β) α β where
instance (priority := 10000) : IsLogHom (α ↪ₘ+ β) α β where
instance (priority := 10000) : IsExpHom (α ↪ₐ* β) α β where

instance (priority := 10000) : EquivLike (α ≃* β) α β where
instance (priority := 10000) : EquivLike (α ≃+ β) α β where
instance (priority := 10000) : EquivLike (α ≃ₐ* β) α β where
instance (priority := 10000) : EquivLike (α ≃ₘ+ β) α β where

instance (priority := 10000) : IsOneHom (α ≃* β) α β where
instance (priority := 10000) : IsZeroHom (α ≃+ β) α β where
instance (priority := 10000) : IsLogOneHom (α ≃ₘ+ β) α β where
instance (priority := 10000) : IsExpZeroHom (α ≃ₐ* β) α β where

instance (priority := 10000) : IsMulHom (α ≃* β) α β where
instance (priority := 10000) : IsAddHom (α ≃+ β) α β where
instance (priority := 10000) : IsLogHom (α ≃ₘ+ β) α β where
instance (priority := 10000) : IsExpHom (α ≃ₐ* β) α β where

protected def GroupHom.id (α: Type*) [One α] [Mul α] : α →* α where
  toFun := id
  map_one := rfl
  map_mul _ _ := rfl

@[simp] def GroupHom.apply_id (x: α) : GroupHom.id α x = x := rfl

protected def GroupHom.comp [Mul γ] [One γ] (f: β →* γ) (g: α →* β) : α →* γ where
  toFun := f ∘ g
  map_one := by dsimp; rw [map_one, map_one]
  map_mul _ _ := by dsimp; rw [map_mul g, map_mul]

@[simp] def GroupHom.apply_comp [Mul γ] [One γ] (f: β →* γ) (g: α →* β) (x: α) : f.comp g x = f (g x) := rfl

protected def AddGroupHom.id (α: Type*) [Zero α] [Add α] : α →+ α where
  toFun := id
  map_zero := rfl
  map_add _ _ := rfl

@[simp] def AddGroupHom.apply_id (x: α) : GroupHom.id α x = x := rfl

protected def AddGroupHom.comp [Add γ] [Zero γ] (f: β →+ γ) (g: α →+ β) : α →+ γ where
  toFun := f ∘ g
  map_zero := by dsimp; rw [map_zero, map_zero]
  map_add _ _ := by dsimp; rw [map_add g, map_add]

@[simp] def AddGroupHom.apply_comp [Add γ] [Zero γ] (f: β →+ γ) (g: α →+ β) (x: α) : f.comp g x = f (g x) := rfl

@[ext] def GroupHom.ext (f g: α →* β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h
@[ext] def AddGroupHom.ext (f g: α →+ β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h
@[ext] def LogHom.ext (f g: α →ₘ+ β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h
@[ext] def ExpHom.ext (f g: α →ₐ* β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h

def AddOfMul.mkHom : α →ₘ+ AddOfMul α where
  toFun := mk
  map_one_to_zero := rfl
  map_mul_to_add _ _ := rfl

def AddOfMul.getHom : AddOfMul α →ₐ* α where
  toFun := get
  map_zero_to_one := rfl
  map_add_to_mul _ _ := rfl

def MulOfAdd.mkHom : α →ₐ* MulOfAdd α where
  toFun := mk
  map_zero_to_one := rfl
  map_add_to_mul _ _ := rfl

def MulOfAdd.getHom : MulOfAdd α →ₘ+ α where
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

@[simp] def ZeroEmbedding.apply_toEmbedding (f: α ↪₀ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def OneEmbedding.apply_toEmbedding (f: α ↪₁ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def LogOneEmbedding.apply_toEmbedding (f: α ↪₁₀ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def ExpZeroEmbedding.apply_toEmbedding (f: α ↪₀₁ β) (x: α) : f.toEmbedding x = f x := rfl

@[simp] def AddGroupEmbedding.apply_toEmbedding (f: α ↪+ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def GroupEmbedding.apply_toEmbedding (f: α ↪* β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def LogEmbedding.apply_toEmbedding (f: α ↪ₘ+ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def ExpEmbedding.apply_toEmbedding (f: α ↪ₐ* β) (x: α) : f.toEmbedding x = f x := rfl

@[simp] def ZeroEquiv.apply_toEquiv (f: α ≃₀ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def OneEquiv.apply_toEquiv (f: α ≃₁ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def LogOneEquiv.apply_toEquiv (f: α ≃₁₀ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def ExpZeroEquiv.apply_toEquiv (f: α ≃₀₁ β) (x: α) : f.toEquiv x = f x := rfl

@[simp] def AddGroupEquiv.apply_toEquiv (f: α ≃+ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def GroupEquiv.apply_toEquiv (f: α ≃* β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def LogEquiv.apply_toEquiv (f: α ≃ₘ+ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def ExpEquiv.apply_toEquiv (f: α ≃ₐ* β) (x: α) : f.toEquiv x = f x := rfl

def ZeroEmbedding.comp (f: β ↪₀ γ) (g: α ↪₀ β) : α ↪₀ γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_zero := by
    dsimp
    rw [map_zero, map_zero]
def OneEmbedding.comp (f: β ↪₁ γ) (g: α ↪₁ β) : α ↪₁ γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_one := by
    dsimp
    rw [map_one, map_one]

def AddGroupEmbedding.comp (f: β ↪+ γ) (g: α ↪+ β) : α ↪+ γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_zero := map_zero (f.toZeroEmbedding.comp g.toZeroEmbedding)
  map_add := map_add (f.toAddEmbedding.comp g.toAddEmbedding)
def GroupEmbedding.comp (f: β ↪* γ) (g: α ↪* β) : α ↪* γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_one := map_one (f.toOneEmbedding.comp g.toOneEmbedding)
  map_mul := map_mul (f.toMulEmbedding.comp g.toMulEmbedding)

def ZeroEquiv.comp (f: β ≃₀ γ) (g: α ≃₀ β) : α ≃₀ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_zero := by
    dsimp
    rw [map_zero, map_zero]
def OneEquiv.comp (f: β ≃₁ γ) (g: α ≃₁ β) : α ≃₁ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_one := by
    dsimp
    rw [map_one, map_one]
def compExpZeroLogOne (f: β ≃₀₁ γ) (g: α ≃₁₀ β) : α ≃₁ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_one := by
    dsimp
    rw [map_one_to_zero, map_zero_to_one]
def compLogOneExpZero (f: β ≃₁₀ γ) (g: α ≃₀₁ β) : α ≃₀ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_zero := by
    dsimp
    rw [map_zero_to_one, map_one_to_zero]

def AddGroupEquiv.comp (f: β ≃+ γ) (g: α ≃+ β) : α ≃+ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_zero := map_zero (f.toZeroEquiv.comp g.toZeroEquiv)
  map_add := map_add (f.toAddEquiv.comp g.toAddEquiv)
def GroupEquiv.comp (f: β ≃* γ) (g: α ≃* β) : α ≃* γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_one := map_one (f.toOneEquiv.comp g.toOneEquiv)
  map_mul := map_mul (f.toMulEquiv.comp g.toMulEquiv)
def compExpLog (f: β ≃ₐ* γ) (g: α ≃ₘ+ β) : α ≃* γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_one := map_one (compExpZeroLogOne f.toExpZeroEquiv g.toLogOneEquiv)
  map_mul := map_mul (eqvCompPreExpLog f.toPreExpEquiv g.toPreLogEquiv)
def compLogExp (f: β ≃ₘ+ γ) (g: α ≃ₐ* β) : α ≃+ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_zero := map_zero (compLogOneExpZero f.toLogOneEquiv g.toExpZeroEquiv)
  map_add := map_add (eqvCompPreLogExp f.toPreLogEquiv g.toPreExpEquiv)

@[simp] def ZeroEmbedding.apply_comp (f: β ↪₀ γ) (g: α ↪₀ β) : (comp f g) x = f (g x) := rfl
@[simp] def OneEmbedding.apply_comp (f: β ↪₁ γ) (g: α ↪₁ β) : (comp f g) x = f (g x) := rfl

@[simp] def AddGroupEmbedding.apply_comp (f: β ↪+ γ) (g: α ↪+ β) : (comp f g) x = f (g x) := rfl
@[simp] def GroupEmbedding.apply_comp (f: β ↪* γ) (g: α ↪* β) : (comp f g) x = f (g x) := rfl

@[simp] def ZeroEquiv.apply_comp (f: β ≃₀ γ) (g: α ≃₀ β) : (comp f g) x = f (g x) := rfl
@[simp] def OneEquiv.apply_comp (f: β ≃₁ γ) (g: α ≃₁ β) : (comp f g) x = f (g x) := rfl
@[simp] def apply_compExpZeroLogOne (f: β ≃₀₁ γ) (g: α ≃₁₀ β) : (compExpZeroLogOne f g) x = f (g x) := rfl
@[simp] def apply_compLogOneExpZero (f: β ≃₁₀ γ) (g: α ≃₀₁ β) : (compLogOneExpZero f g) x = f (g x) := rfl

@[simp] def AddGroupEquiv.apply_comp (f: β ≃+ γ) (g: α ≃+ β) : (comp f g) x = f (g x) := rfl
@[simp] def GroupEquiv.apply_comp (f: β ≃* γ) (g: α ≃* β) : (comp f g) x = f (g x) := rfl
@[simp] def apply_compExpLog (f: β ≃ₐ* γ) (g: α ≃ₘ+ β) : (compExpLog f g) x = f (g x) := rfl
@[simp] def apply_compLogExp (f: β ≃ₘ+ γ) (g: α ≃ₐ* β) : (compLogExp f g) x = f (g x) := rfl

def ZeroEmbedding.trans (g: α ↪₀ β) (f: β ↪₀ γ) : α ↪₀ γ := f.comp g
def OneEmbedding.trans (g: α ↪₁ β) (f: β ↪₁ γ) : α ↪₁ γ := f.comp g

def AddGroupEmbedding.trans (g: α ↪+ β) (f: β ↪+ γ) : α ↪+ γ := f.comp g
def GroupEmbedding.trans (g: α ↪* β) (f: β ↪* γ) : α ↪* γ := f.comp g

def ZeroEquiv.trans (g: α ≃₀ β) (f: β ≃₀ γ) : α ≃₀ γ := f.comp g
def OneEquiv.trans (g: α ≃₁ β) (f: β ≃₁ γ) : α ≃₁ γ := f.comp g
def transExpZeroLogOne (g: α ≃₁₀ β) (f: β ≃₀₁ γ) : α ≃₁ γ := compExpZeroLogOne f g
def transLogOneExpZero (g: α ≃₀₁ β) (f: β ≃₁₀ γ) : α ≃₀ γ := compLogOneExpZero f g

def AddGroupEquiv.trans (g: α ≃+ β) (f: β ≃+ γ) : α ≃+ γ := f.comp g
def GroupEquiv.trans (g: α ≃* β) (f: β ≃* γ) : α ≃* γ := f.comp g
def transExpLog (g: α ≃ₘ+ β) (f: β ≃ₐ* γ) : α ≃* γ := compExpLog f g
def transLogExp (g: α ≃ₐ* β) (f: β ≃ₘ+ γ) : α ≃+ γ := compLogExp f g

@[simp] def ZeroEmbedding.apply_trans (f: β ↪₀ γ) (g: α ↪₀ β) : (trans g f) x = f (g x) := rfl
@[simp] def OneEmbedding.apply_trans (f: β ↪₁ γ) (g: α ↪₁ β) : (trans g f) x = f (g x) := rfl

@[simp] def AddGroupEmbedding.apply_trans (f: β ↪+ γ) (g: α ↪+ β) : (trans g f) x = f (g x) := rfl
@[simp] def GroupEmbedding.apply_trans (f: β ↪* γ) (g: α ↪* β) : (trans g f) x = f (g x) := rfl

@[simp] def ZeroEquiv.apply_trans (f: β ≃₀ γ) (g: α ≃₀ β) : (trans g f) x = f (g x) := rfl
@[simp] def OneEquiv.apply_trans (f: β ≃₁ γ) (g: α ≃₁ β) : (trans g f) x = f (g x) := rfl
@[simp] def apply_transExpZeroLogOne (f: β ≃₀₁ γ) (g: α ≃₁₀ β) : (transExpZeroLogOne g f) x = f (g x) := rfl
@[simp] def apply_transLogOneExpZero (f: β ≃₁₀ γ) (g: α ≃₀₁ β) : (transLogOneExpZero g f) x = f (g x) := rfl

@[simp] def AddGroupEquiv.apply_trans (f: β ≃+ γ) (g: α ≃+ β) : (trans g f) x = f (g x) := rfl
@[simp] def GroupEquiv.apply_trans (f: β ≃* γ) (g: α ≃* β) : (trans g f) x = f (g x) := rfl
@[simp] def apply_transExpLog (f: β ≃ₐ* γ) (g: α ≃ₘ+ β) : (transExpLog g f) x = f (g x) := rfl
@[simp] def apply_transLogExp (f: β ≃ₘ+ γ) (g: α ≃ₐ* β) : (transLogExp g f) x = f (g x) := rfl

def ZeroEquiv.symm (f: α ≃₀ β) : β ≃₀ α where
  toEquiv := f.toEquiv.symm
  map_zero := by
    apply f.inj; dsimp
    rw (occs := [2]) [map_zero]
    apply Eq.trans; apply Equiv.symm_coe
    congr <;> (symm; apply Equiv.symm_coe)
def OneEquiv.symm (f: α ≃₁ β) : β ≃₁ α where
  toEquiv := f.toEquiv.symm
  map_one := by
    apply f.inj; dsimp
    rw (occs := [2]) [map_one]
    apply Eq.trans; apply Equiv.symm_coe
    congr <;> (symm; apply Equiv.symm_coe)

def AddGroupEquiv.symm (f: α ≃+ β) : β ≃+ α where
  toEquiv := f.toEquiv.symm
  map_zero := map_zero f.toZeroEquiv.symm
  map_add := map_add f.toAddEquiv.symm
def GroupEquiv.symm (f: α ≃* β) : β ≃* α where
  toEquiv := f.toEquiv.symm
  map_one := map_one f.toOneEquiv.symm
  map_mul := map_mul f.toMulEquiv.symm

@[simp] def AddGroupEquiv.coe_symm (f: α ≃+ β) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def AddGroupEquiv.symm_coe (f: α ≃+ β) : f (f.symm x) = x := Equiv.symm_coe _ _
@[simp] def GroupEquiv.coe_symm (f: α ≃* β) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def GroupEquiv.symm_coe (f: α ≃* β) : f (f.symm x) = x := Equiv.symm_coe _ _

def AddGroupEmbedding.refl (α: Type*) [Zero α] [Add α] : α ↪+ α where
  toEmbedding := Embedding.id _
  map_zero := rfl
  map_add _ _ := rfl
def GroupEmbedding.refl (α: Type*) [One α] [Mul α] : α ↪* α where
  toEmbedding := Embedding.id _
  map_one := rfl
  map_mul _ _ := rfl

def AddGroupEquiv.refl (α: Type*) [Zero α] [Add α] : α ≃+ α where
  toEquiv := Equiv.id _
  map_zero := rfl
  map_add _ _ := rfl
def GroupEquiv.refl (α: Type*) [One α] [Mul α] : α ≃* α where
  toEquiv := Equiv.id _
  map_one := rfl
  map_mul _ _ := rfl

@[simp] def AddGroupEmbedding.apply_refl (x: α) : AddGroupEmbedding.refl _ x = x := rfl
@[simp] def GroupEmbedding.apply_refl (x: α) : GroupEmbedding.refl _ x = x := rfl

@[simp] def AddGroupEquiv.apply_refl (x: α) : AddGroupEquiv.refl _ x = x := rfl
@[simp] def GroupEquiv.apply_refl (x: α) : GroupEquiv.refl _ x = x := rfl

private class AddGroupEquiv.Ops (α: Type*) extends Add α, Zero α where
private instance : EquivOpsCheck AddGroupEquiv.Ops (fun α β _ _ => α ≃+ β) where
  comp := AddGroupEquiv.comp
  trans := AddGroupEquiv.trans
  symm := AddGroupEquiv.symm
  refl _ := AddGroupEquiv.refl _

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

instance [IsLawfulOneMul α] : IsLawfulOneMul (MulOpp α) where
  one_mul := mul_one (α := α)
  mul_one := one_mul (α := α)

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

instance : IsMonoid (MulOpp α) where
  npow_zero a := by
    induction a using MulOpp.induction with | mk a =>
    show MulOpp.mk (a ^ 0) = MulOpp.mk 1
    rw [npow_zero]
  npow_succ a n := by
    induction a using MulOpp.induction with | mk a =>
    show MulOpp.mk (a ^ (n + 1)) = MulOpp.mk (a * a ^ n)
    rw [npow_succ, mul_comm]

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

def npowAtHom (a: α) : ℕ →ₐ* α where
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

def npow_one (a: α) : a ^ (1: ℕ) = a := by
  rw [npow_succ, npow_zero, one_mul]

def one_nsmul (a: α) : (1: ℕ) • a = a :=
  npow_one (α := MulOfAdd α) _

def npow_add (a: α) (n m: ℕ) : a ^ (n + m) = a ^ n * a ^ m := by
  repeat rw [npow_eq_npowAtHom]
  rw [map_add_to_mul]

def add_nsmul (a: α) (n m: ℕ) : (n + m) • a = n • a + m • a :=
  npow_add (α := MulOfAdd α) _ _ _

def npow_mul (a: α) (n m: ℕ) : a ^ (n * m) = (a ^ n) ^ m := by
  induction m with
  | zero => rw [mul_zero, npow_zero, npow_zero]
  | succ m ih => rw [Nat.mul_succ, npow_add, npow_succ, ih]

def mul_nsmul (a: α) (n m: ℕ) : (n * m) • a = m • n • a :=
  npow_mul (α := MulOfAdd α) _ _ _

end

section

variable
  [FunLike F α β] [Zero α] [Zero β] [One α] [One β]
  [IsOneHom F α β] [IsZeroHom F α β] [IsLogOneHom F α β] [IsExpZeroHom F α β]

variable [Add α] [Add β] [Mul α] [Mul β]
  [IsAddHom F α β] [IsMulHom F α β] [IsLogHom F α β] [IsExpHom F α β]

def MulOpp.liftGroupHom (f: F) : MulOpp α →* MulOpp β where
  toFun x := MulOpp.mk (f x.get)
  map_one := map_one f
  map_mul a b := by
    show mk (f (b.get * a.get)) = _
    rw [map_mul]
    rfl

@[simp] def MulOpp.apply_liftGroupHom (f: F) (x: MulOpp α) : MulOpp.liftGroupHom f x = MulOpp.mk (f x.get) := rfl

end

section

instance [Zero α] [Add α] [Zero β] [Add β] [IsLawfulZeroAdd β] : Zero (α →+ β) where
  zero := {
    toFun x := 0
    map_zero := rfl
    map_add a b := by rw [add_zero]
  }

instance [Zero α] [Add α] [Zero β] [Add β] [IsAddSemigroup β] [IsAddComm β] [IsLawfulZeroAdd β]
  : Add (α →+ β) where
  add f g := {
    toFun x := f x + g x
    map_zero := by rw [map_zero, map_zero, add_zero]
    map_add a b := by
      rw [map_add, map_add]
      ac_rfl
  }


variable
   [Zero α] [Add α] [Zero β] [Add β] [IsAddSemigroup β] [IsAddComm β] [IsLawfulZeroAdd β]

instance : IsAddSemigroup (α →+ β) where
  add_assoc _ _ _ := by
    apply DFunLike.ext; intro
    apply add_assoc

instance : IsAddComm (α →+ β) where
  add_comm _ _ := by
    apply DFunLike.ext; intro
    apply add_comm

instance : IsLawfulZeroAdd (α →+ β) where
  add_zero _ := by
    apply DFunLike.ext; intro
    apply add_zero
  zero_add _ := by
    apply DFunLike.ext; intro
    apply zero_add

end

section

variable [RelLike R α] [One α] [Mul α] [IsMulCon R] (r: R)

instance : IsOneHom (AlgQuot.MkHom r) α (AlgQuot r) where
  map_one _ := rfl

instance [IsLawfulOneMul α] : IsLawfulOneMul (AlgQuot r) where
  one_mul a := by
    induction a with | mk a =>
    rw [←map_one (AlgQuot.mk r), ←map_mul, one_mul]
  mul_one a := by
    induction a with | mk a =>
    rw [←map_one (AlgQuot.mk r), ←map_mul, mul_one]

instance [IsCon R] [Zero α] : IsZeroHom (AlgQuot.MkHom r) α (AlgQuot r) where
  map_zero _ := rfl

instance [Zero α] [IsLawfulZeroMul α] : IsLawfulZeroMul (AlgQuot r) where
  zero_mul a := by
    induction a with | mk a =>
    rw [←map_zero (AlgQuot.mk r), ←map_mul, zero_mul]
  mul_zero a := by
    induction a with | mk a =>
    rw [←map_zero (AlgQuot.mk r), ←map_mul, mul_zero]

end

section

variable [RelLike R α] [Zero α] [Add α] [IsAddCon R] (r: R)

instance [IsLawfulZeroAdd α] : IsLawfulZeroAdd (AlgQuot r) where
  zero_add a := by
    induction a with | mk a =>
    rw [←map_zero (AlgQuot.mk r), ←map_add, zero_add]
  add_zero a := by
    induction a with | mk a =>
    rw [←map_zero (AlgQuot.mk r), ←map_add, add_zero]

end

section

variable [RelLike R α] [MonoidOps α] [IsMulCon R] (r: R)

def resp_npow [IsLawfulPowN α] (r: R) (n: ℕ) (a b: α) : r a b -> r (a ^ n) (b ^ n) := by
  intro rab
  induction n with
  | zero =>
    rw [npow_zero, npow_zero]
  | succ n ih =>
    rw [npow_succ, npow_succ]
    apply resp_mul
    assumption
    assumption

instance [IsLawfulPowN α] : IsPowCon R ℕ where
  resp_pow := by
    intro r s a b
    apply resp_npow

instance [IsLawfulPowN α] : IsLawfulPowN (AlgQuot r) where
  npow_zero a := by
    induction a with | mk a =>
    show AlgQuot.mk r (a ^ 0) = _
    rw [npow_zero, map_one]
  npow_succ a n := by
    induction a with | mk a =>
    show AlgQuot.mk r (a ^ (n + 1)) = _
    rw [npow_succ]
    rfl

instance [IsMonoid α] : IsMonoid (AlgQuot r) where

end

section

variable [RelLike R α] [AddMonoidOps α] [IsAddCon R] (r: R)

def resp_nsmul [IsLawfulNSMul α] (r: R) (n: ℕ) (a b: α) : r a b -> r (n • a) (n • b) := by
  intro rab
  induction n with
  | zero =>
    rw [zero_nsmul, zero_nsmul]
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    apply resp_add
    assumption
    assumption

instance [IsLawfulNSMul α] : IsSMulCon R ℕ where
  resp_smul := by
    intro r s a b
    apply resp_nsmul

instance [IsLawfulNSMul α] : IsLawfulNSMul (AlgQuot r) where
  zero_nsmul a := by
    induction a with | mk a =>
    show AlgQuot.mk r (0 • a) = _
    rw [zero_nsmul, map_zero]
  succ_nsmul n a := by
    induction a with | mk a =>
    show AlgQuot.mk r ((n + 1) • a) = _
    rw [succ_nsmul]
    rfl
instance [IsAddMonoid α] : IsAddMonoid (AlgQuot r) where

end

namespace AlgQuot

variable
  [RelLike R α] [MonoidOps α] [IsMonoid α] [IsMulCon R]
  [RelLike S β] [MonoidOps β] [IsMonoid β] [IsMulCon S]
  {r: R} {s: S}

def MkHom.toGroupHom (_: MkHom r) : α →* AlgQuot r where
  toFun := AlgQuot.mk r
  map_one := rfl
  map_mul _ _ := rfl

@[simp] def apply_mkHom_toGroupHom : MkHom.toGroupHom f x = AlgQuot.mk r x := rfl

def liftGroupHom (f: α →* β) (h: ∀x y, r x y -> f x = f y) : AlgQuot r →* β where
  toFun := Quotient.lift f (by
    intro a b ab
    apply h
    assumption)
  map_one := by
    show f 1 = 1
    rw [map_one]
  map_mul a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    show f (a * b) = _
    apply map_mul

def mapGroupHom (f: α →* β) (h: ∀x y, r x y -> s (f x) (f y)) : AlgQuot r →* AlgQuot s :=
  liftGroupHom (r := r) (β := AlgQuot s) ((AlgQuot.mk s).toGroupHom.comp f) <| by
    intro x y rxy
    simp
    apply sound
    apply h
    assumption

@[simp] def liftGroupHom_mk (f: α →* β) {h} : liftGroupHom f h (mk r x) = f x := rfl
@[simp] def mapGroupHom_mk (f: α →* β) {h} : mapGroupHom f h (mk r x) = mk s (f x) := rfl

end AlgQuot

def MulCon.map
  [Mul α] [Mul β] [RelLike S β] [IsMulCon S]
  [FunLike F α β] [IsMulHom F α β]
  {r: α -> α -> Prop} {s: S}
  (f: F) (h: ∀a b, r a b -> s (f a) (f b)) (rab: MulCon.generate r a b) : s (f a) (f b) := by
  induction rab with
  | of => apply h; assumption
  | mul =>
    rw [map_mul, map_mul]
    apply resp_mul
    assumption
    assumption
  | refl => rfl
  | symm =>
    apply Relation.symm
    assumption
  | trans =>
    apply Relation.trans <;> assumption
