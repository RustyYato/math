import LeanMath.Logic.Funlike
import LeanMath.Logic.Nontrivial
import LeanMath.Logic.LEM
import LeanMath.Tactic.AxiomBlame
import LeanMath.Data.Embedding.Defs
import LeanMath.Data.Equiv.Defs
import LeanMath.Data.AddMul.Defs
import LeanMath.Data.Cong.Defs
import LeanMath.Data.Hom
import LeanMath.Data.OfEquiv.Defs

class IsSemigroup (α: Type*) [Mul α] : Prop where
  protected mul_assoc (a b c: α) : (a * b) * c = a * (b * c)

class IsAddSemigroup (α: Type*) [Add α] where
  protected add_assoc (a b c: α) : (a + b) + c = a + (b + c)

def mul_assoc [Mul α] [IsSemigroup α] (a b c: α) : (a * b) * c = a * (b * c) :=
  IsSemigroup.mul_assoc a b c
def add_assoc [Add α] [IsAddSemigroup α] (a b c: α) : (a + b) + c = a + (b + c) :=
  IsAddSemigroup.add_assoc a b c

class IsCommAt {α: Type*} [Mul α] (a b: α) where
  protected mul_comm : a * b = b * a
class IsAddCommAt {α: Type*} [Add α] (a b: α) where
  protected add_comm : a + b = b + a

instance [Mul α] (a: α) : IsCommAt a a where
  mul_comm := rfl
instance [Add α] (a: α) : IsAddCommAt a a where
  add_comm := rfl

class IsComm (α: Type*) [Mul α] where
  protected mul_comm (a b: α) : a * b = b * a
class IsAddComm (α: Type*) [Add α] where
  protected add_comm (a b: α) : a + b = b + a

instance (priority := 1000000) [Mul α] [IsComm α] (a b: α) : IsCommAt a b where
  mul_comm := IsComm.mul_comm a b

instance (priority := 1000000) [Add α] [IsAddComm α] (a b: α) : IsAddCommAt a b where
  add_comm := IsAddComm.add_comm a b

def mul_comm [Mul α] (a b: α) [IsCommAt a b] : a * b = b * a := IsCommAt.mul_comm
def add_comm [Add α] (a b: α) [IsAddCommAt a b] : a + b = b + a := IsAddCommAt.add_comm

instance (priority := 10) [Mul α] (a b: α) [IsCommAt a b] : IsCommAt b a where
  mul_comm := by
    rw [mul_comm a]

instance (priority := 10) [Add α] (a b: α) [IsAddCommAt a b] : IsAddCommAt b a where
  add_comm := by
    rw [add_comm a]

class IsLeftCancel (α: Type*) [Mul α] where
  protected of_mul_left {k a b: α} : k * a = k * b -> a = b
class IsRightCancel (α: Type*) [Mul α] where
  protected of_mul_right {k a b: α} : a * k = b * k -> a = b

def of_mul_left [Mul α] [IsLeftCancel α] {k a b: α} : k * a = k * b -> a = b :=
  IsLeftCancel.of_mul_left
def of_mul_right [Mul α] [IsRightCancel α] {k a b: α} : a * k = b * k -> a = b :=
  IsRightCancel.of_mul_right

class IsLeftAddCancel (α: Type*) [Add α] where
  protected of_add_left {k a b: α} : k + a = k + b -> a = b
class IsRightAddCancel (α: Type*) [Add α] where
  protected of_add_right {k a b: α} : a + k = b + k -> a = b

def of_add_left [Add α] [IsLeftAddCancel α] {k a b: α} : k + a = k + b -> a = b :=
  IsLeftAddCancel.of_add_left
def of_add_right [Add α] [IsRightAddCancel α] {k a b: α} : a + k = b + k -> a = b :=
  IsRightAddCancel.of_add_right

class IsLeftCancel₀ (α: Type*) [Mul α] [Zero α] where
  protected of_mul_left₀ {k a b: α} : k ≠ 0 -> k * a = k * b -> a = b
class IsRightCancel₀ (α: Type*) [Mul α] [Zero α] where
  protected of_mul_right₀ {k a b: α} : k ≠ 0 -> a * k = b * k -> a = b

def of_mul_left₀ [Mul α] [Zero α] [IsLeftCancel₀ α] {k a b: α} : k ≠ 0 -> k * a = k * b -> a = b :=
  IsLeftCancel₀.of_mul_left₀
def of_mul_right₀ [Mul α] [Zero α] [IsRightCancel₀ α] {k a b: α} : k ≠ 0 -> a * k = b * k -> a = b :=
  IsRightCancel₀.of_mul_right₀

class IsMulHom (F α β: Type*) [FunLike F α β] [Mul α] [Mul β] where
  protected map_mul (f: F) (a₀ a₁: α) : f (a₀ * a₁) = f a₀ * f a₁ := by intro f; exact f.map_mul
class IsAddHom (F α β: Type*) [FunLike F α β] [Add α] [Add β] where
  protected map_add (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ + f a₁ := by intro f; exact f.map_add
class IsLogHom (F α β: Type*) [FunLike F α β] [Mul α] [Add β] where
  protected map_mul_to_add (f: F) (a₀ a₁: α) : f (a₀ * a₁) = f a₀ + f a₁ := by intro f; exact f.map_mul_to_add
class IsExpHom (F α β: Type*) [FunLike F α β] [Add α] [Mul β] where
  protected map_add_to_mul (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ * f a₁  := by intro f; exact f.map_add_to_mul

structure MulHom (α β: Type*) [Mul α] [Mul β] extends Hom α β where
  protected map_mul (a₀ a₁): toFun (a₀ * a₁) = toFun a₀ * toFun a₁

structure AddHom (α β: Type*) [Add α] [Add β] extends Hom α β where
  protected map_add (a₀ a₁): toFun (a₀ + a₁) = toFun a₀ + toFun a₁

class IsSMulHom (F R α β: Type*) [FunLike F α β] [SMul R α] [SMul R β] : Prop where
  protected map_smul (f: F) (r: R) (a: α) : f (r • a) = r • f a := by intro f; exact f.map_smul

structure SMulHom (R α β: Type*) [SMul R α] [SMul R β] extends Hom α β where
  protected map_smul (r: R) (a: α) : toFun (r • a) = r • toFun a

structure SMulEquiv (R α β: Type*) [SMul R α] [SMul R β] extends α ≃ β, SMulHom R α β where

structure PreLogHom (α β: Type*) [Mul α] [Add β] extends Hom α β where
  protected map_mul_to_add (a₀ a₁): toFun (a₀ * a₁) = toFun a₀ + toFun a₁

structure PreExpHom (α β: Type*) [Add α] [Mul β] extends Hom α β where
  protected map_add_to_mul (a₀ a₁): toFun (a₀ + a₁) = toFun a₀ * toFun a₁

structure MulEmbedding (α β: Type*) [Mul α] [Mul β] extends α ↪ β, MulHom α β where
structure AddEmbedding (α β: Type*) [Add α] [Add β] extends α ↪ β, AddHom α β where
structure PreLogEmbedding (α β: Type*) [Mul α] [Add β] extends α ↪ β, PreLogHom α β where
structure PreExpEmbedding (α β: Type*) [Add α] [Mul β] extends α ↪ β, PreExpHom α β where

structure MulEquiv (α β: Type*) [Mul α] [Mul β] extends α ≃ β, MulHom α β where
structure AddEquiv (α β: Type*) [Add α] [Add β] extends α ≃ β, AddHom α β where
structure PreLogEquiv (α β: Type*) [Mul α] [Add β] extends α ≃ β, PreLogHom α β where
structure PreExpEquiv (α β: Type*) [Add α] [Mul β] extends α ≃ β, PreExpHom α β where

infixr:80 " →*ₙ " => MulHom
infixr:80 " →+ₙ " => AddHom
infixr:80 " →ₘ+ₙ " => PreLogHom
infixr:80 " →ₐ*ₙ " => PreExpHom

infixr:80 " ↪*ₙ " => MulEmbedding
infixr:80 " ↪+ₙ " => AddEmbedding
infixr:80 " ↪ₘ+ₙ " => PreLogEmbedding
infixr:80 " ↪ₐ*ₙ " => PreExpEmbedding

infixr:80 " ≃*ₙ " => MulEquiv
infixr:80 " ≃+ₙ " => AddEquiv
infixr:80 " ≃ₘ+ₙ " => PreLogEquiv
infixr:80 " ≃ₐ*ₙ " => PreExpEquiv

section

variable
  [FunLike F α β] [Add α] [Add β] [Add γ] [Mul α] [Mul β] [Mul γ]
  [IsMulHom F α β] [IsAddHom F α β] [IsLogHom F α β] [IsExpHom F α β]
  [SMul R α] [SMul R β] [IsSMulHom F R α β]

def map_mul (f: F) (a₀ a₁: α) : f (a₀ * a₁) =f a₀ * f a₁ := IsMulHom.map_mul f a₀ a₁

def map_add (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ + f a₁ := IsAddHom.map_add f a₀ a₁

def map_smul (f: F) (r: R) (a: α) : f (r • a) = r • f a := IsSMulHom.map_smul _ _ _

def map_mul_to_add (f: F) (a₀ a₁: α) : f (a₀ * a₁) = f a₀ + f a₁ := IsLogHom.map_mul_to_add f a₀ a₁

def map_add_to_mul (f: F) (a₀ a₁: α) : f (a₀ + a₁) = f a₀ * f a₁ := IsExpHom.map_add_to_mul f a₀ a₁

instance : FunLike (SMulHom R α β) α β where
instance : IsSMulHom (SMulHom R α β) R α β where

instance : FunLike (SMulEquiv R α β) α β where
instance : IsSMulHom (SMulEquiv R α β) R α β where

instance (priority := 10000) : FunLike (α →*ₙ β) α β where
instance (priority := 10000) : FunLike (α →+ₙ β) α β where
instance (priority := 10000) : FunLike (α →ₐ*ₙ β) α β where
instance (priority := 10000) : FunLike (α →ₘ+ₙ β) α β where

instance (priority := 10000) : IsMulHom (α →*ₙ β) α β where
instance (priority := 10000) : IsAddHom (α →+ₙ β) α β where
instance (priority := 10000) : IsLogHom (α →ₘ+ₙ β) α β where
instance (priority := 10000) : IsExpHom (α →ₐ*ₙ β) α β where

instance (priority := 10000) : EmbeddingLike (α ↪*ₙ β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪+ₙ β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪ₐ*ₙ β) α β where
instance (priority := 10000) : EmbeddingLike (α ↪ₘ+ₙ β) α β where

instance (priority := 10000) : IsMulHom (α ↪*ₙ β) α β where
instance (priority := 10000) : IsAddHom (α ↪+ₙ β) α β where
instance (priority := 10000) : IsLogHom (α ↪ₘ+ₙ β) α β where
instance (priority := 10000) : IsExpHom (α ↪ₐ*ₙ β) α β where

instance (priority := 10000) : EquivLike (α ≃*ₙ β) α β where
instance (priority := 10000) : EquivLike (α ≃+ₙ β) α β where
instance (priority := 10000) : EquivLike (α ≃ₐ*ₙ β) α β where
instance (priority := 10000) : EquivLike (α ≃ₘ+ₙ β) α β where

instance (priority := 10000) : IsMulHom (α ≃*ₙ β) α β where
instance (priority := 10000) : IsAddHom (α ≃+ₙ β) α β where
instance (priority := 10000) : IsLogHom (α ≃ₘ+ₙ β) α β where
instance (priority := 10000) : IsExpHom (α ≃ₐ*ₙ β) α β where

attribute [local irreducible] AddOfMul MulOfAdd

def AddOfMul.mkHomₙ : α ≃ₘ+ₙ AddOfMul α where
  toEquiv := AddOfMul.equiv
  map_mul_to_add _ _ := rfl

def AddOfMul.getHomₙ : AddOfMul α ≃ₐ*ₙ α where
  toEquiv := AddOfMul.equiv.symm
  map_add_to_mul _ _ := rfl

def MulOfAdd.mkHomₙ : α ≃ₐ*ₙ MulOfAdd α where
  toEquiv := MulOfAdd.equiv
  map_add_to_mul _ _ := rfl

def MulOfAdd.getHomₙ : MulOfAdd α ≃ₘ+ₙ α where
  toEquiv := MulOfAdd.equiv.symm
  map_mul_to_add _ _ := rfl

def AddOfMul.mk_get_homₙ (a: α) : getHomₙ (mkHomₙ a) = a := rfl
def MulOfAdd.mk_get_homₙ (a: α) : getHomₙ (mkHomₙ a) = a := rfl

def AddOfMul.get_mk_homₙ (a: AddOfMul α) : mkHomₙ (getHomₙ a) = a := rfl
def MulOfAdd.get_mk_homₙ (a: MulOfAdd α) : mkHomₙ (getHomₙ a) = a := rfl

@[simp] def AddEmbedding.apply_toEmbedding (f: α ↪+ₙ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def MulEmbedding.apply_toEmbedding (f: α ↪*ₙ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def PreLogEmbedding.apply_toEmbedding (f: α ↪ₘ+ₙ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] def PreExpEmbedding.apply_toEmbedding (f: α ↪ₐ*ₙ β) (x: α) : f.toEmbedding x = f x := rfl

@[simp] def AddEquiv.apply_toEquiv (f: α ≃+ₙ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def MulEquiv.apply_toEquiv (f: α ≃*ₙ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def PreLogEquiv.apply_toEquiv (f: α ≃ₘ+ₙ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] def PreExpEquiv.apply_toEquiv (f: α ≃ₐ*ₙ β) (x: α) : f.toEquiv x = f x := rfl

def AddHom.comp (f: β →+ₙ γ) (g: α →+ₙ β) : α →+ₙ γ where
  toFun := f ∘ g
  map_add a b := by
    dsimp
    rw [map_add, map_add]
def MulHom.comp (f: β →*ₙ γ) (g: α →*ₙ β) : α →*ₙ γ where
  toFun := f ∘ g
  map_mul a b := by
    dsimp
    rw [map_mul, map_mul]

def AddEmbedding.comp (f: β ↪+ₙ γ) (g: α ↪+ₙ β) : α ↪+ₙ γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_add a b := by
    dsimp
    rw [map_add, map_add]
def MulEmbedding.comp (f: β ↪*ₙ γ) (g: α ↪*ₙ β) : α ↪*ₙ γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_mul a b := by
    dsimp
    rw [map_mul, map_mul]

def AddEquiv.comp (f: β ≃+ₙ γ) (g: α ≃+ₙ β) : α ≃+ₙ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_add a b := by
    dsimp
    rw [map_add, map_add]
def MulEquiv.comp (f: β ≃*ₙ γ) (g: α ≃*ₙ β) : α ≃*ₙ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_mul a b := by
    dsimp
    rw [map_mul, map_mul]
def eqvCompPreExpLog (f: β ≃ₐ*ₙ γ) (g: α ≃ₘ+ₙ β) : α ≃*ₙ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_mul a b := by
    dsimp
    rw [map_mul_to_add, map_add_to_mul]
def eqvCompPreLogExp (f: β ≃ₘ+ₙ γ) (g: α ≃ₐ*ₙ β) : α ≃+ₙ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_add a b := by
    dsimp
    rw [map_add_to_mul, map_mul_to_add]

@[simp] def AddEmbedding.apply_comp (f: β ↪+ₙ γ) (g: α ↪+ₙ β) : (f.comp g) x = f (g x) := rfl
@[simp] def MulEmbedding.apply_comp (f: β ↪*ₙ γ) (g: α ↪*ₙ β) : (f.comp g) x = f (g x) := rfl

@[simp] def AddEquiv.apply_comp (f: β ≃+ₙ γ) (g: α ≃+ₙ β) : (f.comp g) x = f (g x) := rfl
@[simp] def MulEquiv.apply_comp (f: β ≃*ₙ γ) (g: α ≃*ₙ β) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_compPreExpLog (f: β ≃ₐ*ₙ γ) (g: α ≃ₘ+ₙ β) : (eqvCompPreExpLog f g) x = f (g x) := rfl
@[simp] def apply_compPreLogExp (f: β ≃ₘ+ₙ γ) (g: α ≃ₐ*ₙ β) : (eqvCompPreLogExp f g) x = f (g x) := rfl

def AddEmbedding.trans (g: α ↪+ₙ β) (f: β ↪+ₙ γ) : α ↪+ₙ γ := f.comp g
def MulEmbedding.trans (g: α ↪*ₙ β) (f: β ↪*ₙ γ) : α ↪*ₙ γ := f.comp g
def AddEquiv.trans (g: α ≃+ₙ β) (f: β ≃+ₙ γ) : α ≃+ₙ γ := f.comp g
def MulEquiv.trans (g: α ≃*ₙ β) (f: β ≃*ₙ γ) : α ≃*ₙ γ := f.comp g
def transPreExpLog (g: α ≃ₘ+ₙ β) (f: β ≃ₐ*ₙ γ) : α ≃*ₙ γ := eqvCompPreExpLog f g
def transPreLogExp (g: α ≃ₐ*ₙ β) (f: β ≃ₘ+ₙ γ) : α ≃+ₙ γ := eqvCompPreLogExp f g

@[simp] def AddEmbedding.apply_trans (g: α ↪+ₙ β) (f: β ↪+ₙ γ) : (g.trans f) x = f (g x) := rfl
@[simp] def MulEmbedding.apply_trans (g: α ↪*ₙ β) (f: β ↪*ₙ γ) : (g.trans f) x = f (g x) := rfl
@[simp] def AddEquiv.apply_trans (g: α ≃+ₙ β) (f: β ≃+ₙ γ) : (g.trans f) x = f (g x) := rfl
@[simp] def MulEquiv.apply_trans (g: α ≃*ₙ β) (f: β ≃*ₙ γ) : (g.trans f) x = f (g x) := rfl
@[simp] def apply_transPreExpLog (g: α ≃ₘ+ₙ β) (f: β ≃ₐ*ₙ γ) : (transPreExpLog g f) x = f (g x) := rfl
@[simp] def apply_transPreLogExp (g: α ≃ₐ*ₙ β) (f: β ≃ₘ+ₙ γ) : (transPreLogExp g f) x = f (g x) := rfl

def AddEquiv.symm (f: α ≃+ₙ β) : β ≃+ₙ α where
  toEquiv := f.toEquiv.symm
  map_add a b := by
    apply f.inj; dsimp
    rw (occs := [2]) [map_add]
    apply Eq.trans; apply Equiv.symm_coe
    congr <;> (symm; apply Equiv.symm_coe)
def MulEquiv.symm (f: α ≃*ₙ β) : β ≃*ₙ α where
  toEquiv := f.toEquiv.symm
  map_mul a b := by
    apply f.inj; dsimp
    rw (occs := [2]) [map_mul]
    apply Eq.trans; apply Equiv.symm_coe
    congr <;> (symm; apply Equiv.symm_coe)

@[simp] def AddEquiv.coe_symm (f: α ≃+ₙ β) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def AddEquiv.symm_coe (f: α ≃+ₙ β) : f (f.symm x) = x := Equiv.symm_coe _ _
@[simp] def MulEquiv.coe_symm (f: α ≃*ₙ β) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def MulEquiv.symm_coe (f: α ≃*ₙ β) : f (f.symm x) = x := Equiv.symm_coe _ _

def AddEmbedding.refl (α: Type*) [Add α] : α ↪+ₙ α where
  toEmbedding := Embedding.id _
  map_add _ _ := rfl
def MulEmbedding.refl (α: Type*) [Mul α] : α ↪*ₙ α where
  toEmbedding := Embedding.id _
  map_mul _ _ := rfl

def AddEquiv.refl (α: Type*) [Add α] : α ≃+ₙ α where
  toEquiv := Equiv.id _
  map_add _ _ := rfl
def MulEquiv.refl (α: Type*) [Mul α] : α ≃*ₙ α where
  toEquiv := Equiv.id _
  map_mul _ _ := rfl

@[simp] def AddEmbedding.apply_refl (x: α) : AddEmbedding.refl _ x = x := rfl
@[simp] def MulEmbedding.apply_refl (x: α) : MulEmbedding.refl _ x = x := rfl

@[simp] def AddEquiv.apply_refl (x: α) : AddEquiv.refl _ x = x := rfl
@[simp] def MulEquiv.apply_refl (x: α) : MulEquiv.refl _ x = x := rfl

private instance : EmbeddingOpsCheck Add (fun α β _ _ => α ↪+ₙ β) where
  comp := AddEmbedding.comp
  trans := AddEmbedding.trans
  refl := AddEmbedding.refl

private instance : EmbeddingOpsCheck Mul (fun α β _ _ => α ↪*ₙ β) where
  comp := MulEmbedding.comp
  trans := MulEmbedding.trans
  refl := MulEmbedding.refl

private instance : EquivOpsCheck Add (fun α β _ _ => α ≃+ₙ β) where
  comp := AddEquiv.comp
  trans := AddEquiv.trans
  symm := AddEquiv.symm
  refl := AddEquiv.refl
private instance : EquivOpsCheck Mul (fun α β _ _ => α ≃*ₙ β) where
  comp := MulEquiv.comp
  trans := MulEquiv.trans
  symm := MulEquiv.symm
  refl := MulEquiv.refl

end

instance : IsSemigroup Nat where
  mul_assoc := Nat.mul_assoc
instance : IsSemigroup Int where
  mul_assoc := Int.mul_assoc
instance : IsAddSemigroup Nat where
  add_assoc := Nat.add_assoc
instance : IsAddSemigroup Int where
  add_assoc := Int.add_assoc

instance : IsComm Nat where
  mul_comm := Nat.mul_comm
instance : IsComm Int where
  mul_comm := Int.mul_comm
instance : IsAddComm Nat where
  add_comm := Nat.add_comm
instance : IsAddComm Int where
  add_comm := Int.add_comm

instance [Mul α] [IsSemigroup α] : Std.Associative (α := α) (· * ·) where
  assoc := mul_assoc
instance [Add α] [IsAddSemigroup α] : Std.Associative (α := α) (· + ·) where
  assoc := add_assoc
instance [Mul α] [IsComm α] : Std.Commutative (α := α) (· * ·) where
  comm _ _ := mul_comm _ _
instance [Add α] [IsAddComm α] : Std.Commutative (α := α) (· + ·) where
  comm _ _ := add_comm _ _

section

variable [Add α] [Mul α] [IsSemigroup α] [IsAddSemigroup α]

instance : IsSemigroup (MulOfAdd α) where
  mul_assoc := IsAddSemigroup.add_assoc (α := α)
instance : IsAddSemigroup (AddOfMul α) where
  add_assoc := IsSemigroup.mul_assoc (α := α)

instance : IsSemigroup (MulOpp α) where
  mul_assoc a b c := by
    induction a using MulOpp.induction with | mk a =>
    induction b using MulOpp.induction with | mk b =>
    induction c using MulOpp.induction with | mk c =>
    show (MulOpp.mk (c * (b * a))) = MulOpp.mk ((c * b) * a)
    rw [mul_assoc]

instance [IsAddComm α] : IsComm (MulOfAdd α) where
  mul_comm := IsAddComm.add_comm (α := α)
instance [IsComm α] : IsAddComm (AddOfMul α) where
  add_comm := IsComm.mul_comm (α := α)

instance (a b: α) [IsAddCommAt a b] : IsCommAt (MulOfAdd.mkHomₙ a) (MulOfAdd.mkHomₙ b) where
  mul_comm := IsAddCommAt.add_comm (a := a) (b := b)
instance (a b: α) [IsCommAt a b] : IsAddCommAt (AddOfMul.mkHomₙ a) (AddOfMul.mkHomₙ b) where
  add_comm := IsCommAt.mul_comm (a := a) (b := b)

def mul_left_comm (a b c: α) [IsCommAt a b] : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc, mul_comm a, mul_assoc]
def mul_right_comm (a b c: α) [IsCommAt b c] : a * (b * c) = a * c * b := by
  rw [mul_assoc, mul_comm b, ←mul_assoc]

def add_left_comm (a b c: α) [IsAddCommAt a b] : a + (b + c) = b + (a + c) :=
  mul_left_comm (a := MulOfAdd.mkHomₙ a) (b := MulOfAdd.mkHomₙ b) (c := MulOfAdd.mkHomₙ c)

def add_right_comm (a b c: α) [IsAddCommAt b c] : a + (b + c) = a + c + b :=
  mul_right_comm (a := MulOfAdd.mkHomₙ a) (b := MulOfAdd.mkHomₙ b) (c := MulOfAdd.mkHomₙ c)

def mul_comm_left [Mul α] [IsSemigroup α]
  (a b c: α) [IsCommAt a b] [IsCommAt a c] [IsCommAt b c] : a * b * c = c * b * a := by
  rw [mul_assoc, mul_left_comm, mul_comm _ c, ←mul_assoc, mul_comm b]

def mul_comm_right [Mul α] [IsSemigroup α]
  (a b c: α) [IsCommAt b c] : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm _ c, ←mul_assoc]

def add_comm_right [Add α] [IsAddSemigroup α]
  (a b c: α) [IsAddCommAt b c] : a + b + c = a + c + b := by
  rw [add_assoc, add_comm _ c, ←add_assoc]

def add_comm_left [Add α] [IsAddSemigroup α]
  (a b c: α) [IsAddCommAt a c] [IsAddCommAt b c] [IsAddCommAt a b] : a + b + c = c + b + a := by
  rw [add_assoc, add_left_comm, add_comm _ c, ←add_assoc, add_comm b]

end

instance [RelLike R α] [Mul α] [IsMulCon R] (r: R) : IsMulHom (AlgQuot.MkHom r) α (AlgQuot r) where
  map_mul _ _ _ := rfl
instance [RelLike R α] [Add α] [IsAddCon R] (r: R) : IsAddHom (AlgQuot.MkHom r) α (AlgQuot r) where
  map_add _ _ _ := rfl

instance [RelLike R α] [Mul α] [IsMulCon R] [IsSemigroup α] (r: R) : IsSemigroup (AlgQuot r) where
  mul_assoc a b c := by
    induction a with | mk a =>
    induction b with | mk b =>
    induction c with | mk c =>
    iterate 4 rw [←map_mul]
    rw [mul_assoc]

instance [RelLike R α] [Add α] [IsAddCon R] [IsAddSemigroup α] (r: R) : IsAddSemigroup (AlgQuot r) where
  add_assoc a b c := by
    induction a with | mk a =>
    induction b with | mk b =>
    induction c with | mk c =>
    iterate 4 rw [←map_add]
    rw [add_assoc]

instance [RelLike R α] [Mul α] [IsMulCon R] [IsComm α] (r: R) : IsComm (AlgQuot r) where
  mul_comm a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    iterate 2 rw [←map_mul]
    rw [mul_comm]

instance [RelLike R α] [Add α] [IsAddCon R] [IsAddComm α] (r: R) : IsAddComm (AlgQuot r) where
  add_comm a b := by
    induction a with | mk a =>
    induction b with | mk b =>
    iterate 2 rw [←map_add]
    rw [add_comm]

@[implicit_reducible]
def IsSemigroup.lift [Mul α] [Mul β] [IsSemigroup β] [EmbeddingLike F α β] [IsMulHom F α β] (f: F) : IsSemigroup α where
  mul_assoc a b c := by
    apply inj f
    simp [map_mul, mul_assoc]
@[implicit_reducible]
def IsComm.lift [Mul α] [Mul β] [IsComm β] [EmbeddingLike F α β] [IsMulHom F α β] (f: F) : IsComm α where
  mul_comm a b := by
    apply inj f
    simp [map_mul, mul_comm]

@[implicit_reducible]
def IsAddSemigroup.lift [Add α] [Add β] [IsAddSemigroup β] [EmbeddingLike F α β] [IsAddHom F α β] (f: F) : IsAddSemigroup α where
  add_assoc a b c := by
    apply inj f
    simp [map_add, add_assoc]
@[implicit_reducible]
def IsAddComm.lift [Add α] [Add β] [IsAddComm β] [EmbeddingLike F α β] [IsAddHom F α β] (f: F) : IsAddComm α where
  add_comm a b := by
    apply inj f
    simp [map_add, add_comm]

instance (priority := 100) [Mul α] [Zero α] [IsComm α] [IsLeftCancel₀ α] : IsRightCancel₀ α where
  of_mul_right₀ := by intro k _ _ hk h; rw [mul_comm _ k, mul_comm _ k] at h; exact of_mul_left₀ hk h
instance (priority := 100) [Mul α] [Zero α] [IsComm α] [IsRightCancel₀ α] : IsLeftCancel₀ α where
  of_mul_left₀ := by intro k _ _ hk h; rw [mul_comm k, mul_comm k] at h; exact of_mul_right₀ hk h

instance (priority := 100) [Mul α] [IsComm α] [IsLeftCancel α] : IsRightCancel α where
  of_mul_right := by intro k _ _ h; rw [mul_comm _ k, mul_comm _ k] at h; exact of_mul_left h
instance (priority := 100) [Mul α] [IsComm α] [IsRightCancel α] : IsLeftCancel α where
  of_mul_left := by intro k _ _ h; rw [mul_comm k, mul_comm k] at h; exact of_mul_right h

instance [Mul α] [IsLeftCancel α] : IsLeftAddCancel (AddOfMul α) where
  of_add_left := of_mul_left (α := α)
instance [Mul α] [IsRightCancel α] : IsRightAddCancel (AddOfMul α) where
  of_add_right := of_mul_right (α := α)

instance [Add α] [IsLeftAddCancel α] : IsLeftCancel (MulOfAdd α) where
  of_mul_left := of_add_left (α := α)
instance [Add α] [IsRightAddCancel α] : IsRightCancel (MulOfAdd α) where
  of_mul_right := of_add_right (α := α)

instance (priority := 100) [Add α] [IsAddComm α] [IsLeftAddCancel α] : IsRightAddCancel α where
  of_add_right := of_mul_right (α := MulOfAdd α)
instance (priority := 100) [Add α] [IsAddComm α] [IsRightAddCancel α] : IsLeftAddCancel α where
  of_add_left := of_mul_left (α := MulOfAdd α)

instance : IsLeftCancel₀ ℕ where
  of_mul_left₀ := by
    intro k a b hk h
    apply Nat.eq_of_mul_eq_mul_left _ h
    apply Nat.pos_of_ne_zero
    assumption

instance : IsLeftCancel₀ ℤ where
  of_mul_left₀ := by
    intro k a b hk h
    apply Int.eq_of_mul_eq_mul_left _ h
    assumption

instance : IsLeftAddCancel ℕ where
  of_add_left := Nat.add_left_cancel

instance : IsLeftAddCancel ℤ where
  of_add_left := Int.add_left_cancel

instance : IsRightCancel₀ ℕ := inferInstance
instance : IsRightCancel₀ ℤ := inferInstance

def smul_eq_mul [Mul α] (a b: α) : a • b = a * b := rfl

namespace OfEquiv

variable (f: α ≃ β)

protected scoped instance mul [Mul β] : Mul (OfEquiv f) where
  mul a b := f.symm (f a * f b)
protected scoped instance add [Add β] : Add (OfEquiv f) where
  add a b := f.symm (f a + f b)

protected scoped instance smul (R: Type*) [SMul R β] : SMul R (OfEquiv f) where
  smul r a := f.symm (r • f a)
protected scoped instance pow (R: Type*) [Pow β R] : Pow (OfEquiv f) R where
  pow a r := f.symm (f a ^ r)

protected scoped instance inv [Inv β] : Inv (OfEquiv f) where
  inv a := f.symm (f a)⁻¹
protected scoped instance neg [Neg β] : Neg (OfEquiv f) where
  neg a := f.symm (-f a)

protected scoped instance div [Div β] : Div (OfEquiv f) where
  div a b := f.symm (f a / f b)
protected scoped instance sub [Sub β] : Sub (OfEquiv f) where
  sub a b := f.symm (f a - f b)

protected scoped instance one [One β] : One (OfEquiv f) where
  one := f.symm 1
protected scoped instance zero [Zero β] : Zero (OfEquiv f) where
  zero := f.symm 0

protected scoped instance natCast [NatCast β] : NatCast (OfEquiv f) where
  natCast n := f.symm n
protected scoped instance intCast [IntCast β] : IntCast (OfEquiv f) where
  intCast n := f.symm n

@[simp] def mul_def [Mul β] (a b: OfEquiv f) : a * b = f.symm (f a * f b) := rfl
@[simp] def add_def [Add β] (a b: OfEquiv f) : a + b = f.symm (f a + f b) := rfl

@[simp] def inv_def [Inv β] (a: OfEquiv f) : a⁻¹ = f.symm (f a)⁻¹ := rfl
@[simp] def neg_def [Neg β] (a: OfEquiv f) : -a = f.symm (-f a) := rfl

@[simp] def div_def [Div β] (a b: OfEquiv f) : a / b = f.symm (f a / f b) := rfl
@[simp] def sub_def [Sub β] (a b: OfEquiv f) : a - b = f.symm (f a - f b) := rfl

@[simp] def smul_def [SMul R β] (r: R) (a: OfEquiv f) : r • a = f.symm (r • f a) := rfl
@[simp] def pow_def [Pow β R] (a: OfEquiv f) (r: R) : a ^ r = f.symm (f a ^ r) := rfl

@[simp] def one_def [One β] : (1: OfEquiv f) = f.symm 1 := rfl
@[simp] def zero_def [Zero β] : (0: OfEquiv f) = f.symm 0 := rfl

@[simp] def natCast_def [NatCast β] (n: ℕ) : (n: OfEquiv f) = f.symm n := rfl
@[simp] def intCast_def [IntCast β] (n: ℤ) : (n: OfEquiv f) = f.symm n := rfl

protected scoped instance IsSemigroup [Mul β] [IsSemigroup β] : IsSemigroup (OfEquiv f) where
  mul_assoc a b c := by
    dsimp; repeat rw [Equiv.symm_coe]
    rw [mul_assoc]

protected scoped instance IsAddSemigroup [Add β] [IsAddSemigroup β] : IsAddSemigroup (OfEquiv f) where
  add_assoc a b c := by
    dsimp; repeat rw [Equiv.symm_coe]
    rw [add_assoc]

protected scoped instance IsComm [Mul β] [IsComm β] : IsComm (OfEquiv f) where
  mul_comm a b := by
    dsimp; repeat rw [Equiv.symm_coe]
    rw [mul_comm]

protected scoped instance IsAddComm [Add β] [IsAddComm β] : IsAddComm (OfEquiv f) where
  add_comm a bc := by
    dsimp; repeat rw [Equiv.symm_coe]
    rw [add_comm]

protected scoped instance IsLeftCancel [Mul β] [IsLeftCancel β] : IsLeftCancel (OfEquiv f) where
  of_mul_left h := by
    dsimp at h
    exact inj f (of_mul_left (inj f.symm h))

protected scoped instance IsRightCancel [Mul β] [IsRightCancel β] : IsRightCancel (OfEquiv f) where
  of_mul_right h := by
    dsimp at h
    exact inj f (of_mul_right (inj f.symm h))

protected scoped instance IsAddLeftCancel [Add β] [IsLeftAddCancel β] : IsLeftAddCancel (OfEquiv f) where
  of_add_left h := by
    dsimp at h
    exact inj f (of_add_left (inj f.symm h))

protected scoped instance IsAddRightCancel [Add β] [IsRightAddCancel β] : IsRightAddCancel (OfEquiv f) where
  of_add_right h := by
    dsimp at h
    exact inj f (of_add_right (inj f.symm h))

protected scoped instance IsLeftCancel₀ [Zero β] [Mul β] [IsLeftCancel₀ β] : IsLeftCancel₀ (OfEquiv f) where
  of_mul_left₀ {k a b} hk h := by
    dsimp at h
    replace hk : f k ≠ 0 := by
      intro h; apply hk
      have := congrArg f.symm h
      rwa [Equiv.coe_symm] at this
    exact inj f (of_mul_left₀ hk (inj f.symm h))

protected scoped instance IsRightCancel₀ [Zero β] [Mul β] [IsRightCancel₀ β] : IsRightCancel₀ (OfEquiv f) where
  of_mul_right₀ {k a b} hk h := by
    dsimp at h
    replace hk : f k ≠ 0 := by
      intro h; apply hk
      have := congrArg f.symm h
      rwa [Equiv.coe_symm] at this
    exact inj f (of_mul_right₀ hk (inj f.symm h))

end OfEquiv
