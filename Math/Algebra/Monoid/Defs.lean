module

public import Math.Algebra.Semigroup.Defs
public import Math.Logic.Nontrivial
public import Math.Logic.LEM

namespace Math

section Property

public class NoZeroDivisors (α: Type*) [Mul α] [Zero α] where
  of_mul_eq_zero {a b: α} (h: a * b = 0) : a = 0 ∨ b = 0

export NoZeroDivisors (of_mul_eq_zero)

public class IsZeroNeOne (α: Type*) [Zero α] [One α] : Prop where
  zero_ne_one : (0: α) ≠ (1: α)

export IsZeroNeOne (zero_ne_one)

public class IsLawfulOne (α: Type*) [Mul α] [One α] : Prop where
  mul_one (a: α) : a * 1 = a
  one_mul (a: α) : 1 * a = a
public class IsLawfulZero (α: Type*) [Add α] [Zero α] : Prop where
  add_zero (a: α) : a + 0 = a
  zero_add (a: α) : 0 + a = a
public class IsLawfulZeroMul (α: Type*) [Mul α] [Zero α] : Prop where
  mul_zero (a: α) : a * 0 = 0
  zero_mul (a: α) : 0 * a = 0
public class IsLawfulPowN (α: Type*) [Pow α ℕ] [Mul α] [One α] : Prop where
  pown_zero (a: α) : a ^ 0 = 1
  pown_succ (a: α) (n: ℕ) : a ^ (n + 1) = a ^ n * a
public class IsLawfulNSMul (α: Type*) [SMul ℕ α] [Add α] [Zero α] : Prop where
  zero_nsmul (a: α) : 0 • a = 0
  succ_nsmul (a: α) (n: ℕ) : (n + 1) • a = n • a + a

export IsLawfulOne (one_mul mul_one)
export IsLawfulZero (zero_add add_zero)
export IsLawfulZeroMul (zero_mul mul_zero)
export IsLawfulPowN (pown_zero pown_succ)
export IsLawfulNSMul (zero_nsmul succ_nsmul)

public instance (priority := 100) NoZeroDivisors.ofLeftCancel₀ [Mul α] [Zero α] [IsLawfulZeroMul α] [IsLeftCancel₀ α] [ExcludedMiddleEq α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply LEM.or_iff_not_imp_left.mpr
    intro ha
    rw [←mul_zero a] at h
    exact of_mul_left₀ ha h
public instance (priority := 100) [Mul α] [Zero α] [IsLawfulZeroMul α] [IsRightCancel₀ α] [ExcludedMiddleEq α] : NoZeroDivisors α where
  of_mul_eq_zero {a b} h := by
    apply LEM.or_iff_not_imp_right.mpr
    intro hb
    rw [←zero_mul b] at h
    exact of_mul_right₀ hb h

public instance [Add α] [Zero α] [IsLawfulZero α] : IsLawfulOne (MulOfAdd α) where
  mul_one := add_zero (α := α)
  one_mul := zero_add (α := α)
public instance [Mul α] [One α] [IsLawfulOne α] : IsLawfulZero (AddOfMul α) where
  add_zero := mul_one (α := α)
  zero_add := one_mul (α := α)

namespace DefaultPowN

public def default_pown [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) : ℕ -> α
| 0 => 1
| n + 1 => default_pown a n * a

public def fast_pown [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) (n: ℕ) : α :=
  if n = 0 then
    1
  else
    let x := fast_pown a (n / 2)
    x * x * (if n % 2 == 0 then 1 else a)

instance [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) (n: ℕ) :
  IsCommAt a (default_pown a n) where
  mul_comm := by
    induction n with
    | zero =>
      unfold default_pown
      rw [mul_one, one_mul]
    | succ n ih =>
      unfold default_pown
      rw [←mul_assoc, ih]

theorem nat_succ_div_two (n: ℕ) : (n + 1) / 2 =
  n / 2 + 1 / 2 + if 2 ≤ n % 2 + 1 % 2 then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 2) / 2 = _
    rw [Nat.add_div_right _ (by decide), ih]
    dsimp; clear ih
    rw [Nat.add_assoc]; congr 1
    rw [Nat.add_mod]
    dsimp
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> (rw [h]; rfl)

theorem default_pown_step_half [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α] (a: α) (n: ℕ) :
  default_pown a n = default_pown a (n / 2) * default_pown a (n / 2) * (if n % 2 == 0 then 1 else a) := by
  induction n with
  | zero =>
    show 1 = 1 * 1 * 1
    iterate 2 rw [mul_one]
  | succ n ih =>
    rw [nat_succ_div_two]
    dsimp; rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [h, show (n + 1) % 2 = 1 by omega]
      rw [default_pown, ih, h]
      dsimp; rw [mul_one]
    · rw [h, show (n + 1) % 2 = 0 by omega]
      dsimp; rw [mul_one]
      unfold default_pown
      rw [ih, h]
      dsimp
      rw [mul_assoc _ _ (_ * _)]
      rw [mul_assoc, mul_assoc]; congr 1
      rw [←mul_assoc, ←mul_assoc]; congr 1
      rw [mul_comm]

@[csimp]
public theorem default_pown_eq_fast_pown : @default_pown = @fast_pown := by
  ext α _ _ _ _ a n
  induction n using fast_pown.induct a with
  | case1 => unfold default_pown fast_pown; dsimp
  | case2 n hn ih =>
    unfold fast_pown; rw [ite_eq_right hn, default_pown_step_half]
    congr

variable [Mul α] [One α] [IsSemigroup α] [IsLawfulOne α]

public scoped instance instPowNat : Pow α ℕ where
  pow := default_pown

public scoped instance : IsLawfulPowN α where
  pown_zero _ := rfl
  pown_succ _ _ := rfl

end DefaultPowN

namespace DefaultNSMul

variable [Add α] [Zero α] [IsAddSemigroup α] [IsLawfulZero α]

open scoped DefaultPowN

public scoped instance : SMul ℕ α where
  smul n a := MulOfAdd.get (Pow.pow (MulOfAdd.mk a) n)

public scoped instance : IsLawfulNSMul α where
  zero_nsmul _ := rfl
  succ_nsmul _ _ := rfl

end DefaultNSMul

public class MonoidOps (α: Type*) extends Mul α, One α where
  toPowN : Pow α ℕ

public instance [MonoidOps α] : Pow α ℕ := MonoidOps.toPowN
public instance (priority := 100) [Pow α ℕ] [Mul α] [One α] : MonoidOps α where
  toPowN := inferInstance

public class AddMonoidOps (α: Type*) extends Add α, Zero α where
  toNSMul : SMul ℕ α

public instance [AddMonoidOps α] : SMul ℕ α := AddMonoidOps.toNSMul
public instance (priority := 100) [SMul ℕ α] [Add α] [Zero α] : AddMonoidOps α where
  toNSMul := inferInstance

public class IsMonoid (α: Type*) [MonoidOps α] extends IsSemigroup α, IsLawfulOne α, IsLawfulPowN α where
public class IsAddMonoid (α: Type*) [AddMonoidOps α] extends IsAddSemigroup α, IsLawfulZero α, IsLawfulNSMul α where

end Property

section Hom

section Defs

public class IsOneHom (F α β: Type*) [Funlike F α β] [One α] [One β] : Prop where
  map_one (f: F) : f 1 = 1 := by intro f; exact f.map_one
public class IsZeroHom (F α β: Type*) [Funlike F α β] [Zero α] [Zero β] : Prop where
  map_zero (f: F) : f 0 = 0 := by intro f; exact f.map_zero
public class IsExpZeroHom (F α β: Type*) [Funlike F α β] [Zero α] [One β] : Prop where
  map_zero_to_one (f: F) : f 0 = 1 := by intro f; exact f.map_zero_to_one
public class IsLogOneHom (F α β: Type*) [Funlike F α β] [One α] [Zero β] : Prop where
  map_one_to_zero (f: F) : f 1 = 0 := by intro f; exact f.map_one_to_zero

export IsOneHom (map_one)
export IsZeroHom (map_zero)
export IsExpZeroHom (map_zero_to_one)
export IsLogOneHom (map_one_to_zero)

public structure OneHom (α β: Type*) [One α] [One β] extends Hom α β where
  protected map_one : toFun 1 = 1
public structure ZeroHom (α β: Type*) [Zero α] [Zero β] extends Hom α β where
  protected map_zero : toFun 0 = 0
public structure ExpZeroHom (α β: Type*) [Zero α] [One β] extends Hom α β where
  protected map_zero_to_one : toFun 0 = 1
public structure LogOneHom (α β: Type*) [One α] [Zero β] extends Hom α β where
  protected map_one_to_zero : toFun 1 = 0

public structure OneEquiv (α β: Type*) [One α] [One β] extends α ≃ β, OneHom α β where
public structure ZeroEquiv (α β: Type*) [Zero α] [Zero β] extends α ≃ β, ZeroHom α β where
public structure ExpZeroEquiv (α β: Type*) [Zero α] [One β] extends α ≃ β, ExpZeroHom α β where
public structure LogOneEquiv (α β: Type*) [One α] [Zero β] extends α ≃ β, LogOneHom α β where

public structure GroupHom (α β: Type*) [Mul α] [One α] [Mul β] [One β] extends MulHom α β, OneHom α β where
public structure AddGroupHom (α β: Type*) [Add α] [Zero α] [Add β] [Zero β] extends AddHom α β, ZeroHom α β where
public structure GroupExpHom (α β: Type*) [Add α] [Zero α] [Mul β] [One β] extends ExpHom α β, ExpZeroHom α β where
public structure GroupLogHom (α β: Type*) [Mul α] [One α] [Add β] [Zero β] extends LogHom α β, LogOneHom α β where

public structure GroupEmbedding (α β: Type*) [Mul α] [One α] [Mul β] [One β] extends α ↪ β, GroupHom α β where
public structure AddGroupEmbedding (α β: Type*) [Add α] [Zero α] [Add β] [Zero β] extends α ↪ β, AddGroupHom α β where
public structure GroupExpEmbedding (α β: Type*) [Add α] [Zero α] [Mul β] [One β] extends α ↪ β, GroupExpHom α β where
public structure GroupLogEmbedding (α β: Type*) [Mul α] [One α] [Add β] [Zero β] extends α ↪ β, GroupLogHom α β where

public structure GroupEquiv (α β: Type*) [Mul α] [One α] [Mul β] [One β] extends α ≃ β, GroupHom α β, MulEquiv α β, OneEquiv α β where
public structure AddGroupEquiv (α β: Type*) [Add α] [Zero α] [Add β] [Zero β] extends α ≃ β, AddGroupHom α β, AddEquiv α β, ZeroEquiv α β where
public structure GroupExpEquiv (α β: Type*) [Add α] [Zero α] [Mul β] [One β] extends α ≃ β, GroupExpHom α β, ExpEquiv α β, ExpZeroEquiv α β where
public structure GroupLogEquiv (α β: Type*) [Mul α] [One α] [Add β] [Zero β] extends α ≃ β, GroupLogHom α β, LogEquiv α β, LogOneEquiv α β where

infixr:80 " →₁ " => OneHom
infixr:80 " →₀ " => ZeroHom
infixr:80 " ≃₁ " => OneEquiv
infixr:80 " ≃₀ " => ZeroEquiv

infixr:80 " →* " => GroupHom
infixr:80 " →+ " => AddGroupHom
infixr:80 " →ₘ+ " => GroupExpHom
infixr:80 " →ₐ* " => GroupLogHom

infixr:80 " ↪* " => GroupEmbedding
infixr:80 " ↪+ " => AddGroupEmbedding
infixr:80 " ↪ₘ+ " => GroupExpEmbedding
infixr:80 " ↪ₐ* " => GroupLogEmbedding

infixr:80 " ≃* " => GroupEquiv
infixr:80 " ≃+ " => AddGroupEquiv
infixr:80 " ≃ₘ+ " => GroupExpEquiv
infixr:80 " ≃ₐ* " => GroupLogEquiv

end Defs

section Impls

variable [Mul α] [Mul β] [Add α] [Add β] [One α] [One β] [Zero α] [Zero β]

public instance : Funlike (OneHom α β) α β where
public instance : Funlike (ZeroHom α β) α β where
public instance : Funlike (ExpZeroHom α β) α β where
public instance : Funlike (LogOneHom α β) α β where
public instance : Funlike (GroupHom α β) α β where
public instance : Funlike (AddGroupHom α β) α β where
public instance : Funlike (GroupExpHom α β) α β where
public instance : Funlike (GroupLogHom α β) α β where

public instance : EmbeddingLike (GroupEmbedding α β) α β where
public instance : EmbeddingLike (AddGroupEmbedding α β) α β where
public instance : EmbeddingLike (GroupExpEmbedding α β) α β where
public instance : EmbeddingLike (GroupLogEmbedding α β) α β where

public instance : EquivLike (OneEquiv α β) α β where
public instance : EquivLike (ZeroEquiv α β) α β where
public instance : EquivLike (ExpZeroEquiv α β) α β where
public instance : EquivLike (LogOneEquiv α β) α β where
public instance : EquivLike (GroupEquiv α β) α β where
public instance : EquivLike (AddGroupEquiv α β) α β where
public instance : EquivLike (GroupExpEquiv α β) α β where
public instance : EquivLike (GroupLogEquiv α β) α β where

public instance : IsOneHom (OneHom α β) α β where
public instance : IsZeroHom (ZeroHom α β) α β where
public instance : IsExpZeroHom (ExpZeroHom α β) α β where
public instance : IsLogOneHom (LogOneHom α β) α β where
public instance : IsOneHom (GroupHom α β) α β where
public instance : IsZeroHom (AddGroupHom α β) α β where
public instance : IsExpZeroHom (GroupExpHom α β) α β where
public instance : IsLogOneHom (GroupLogHom α β) α β where
public instance : IsMulHom (GroupHom α β) α β where
public instance : IsAddHom (AddGroupHom α β) α β where
public instance : IsExpHom (GroupExpHom α β) α β where
public instance : IsLogHom (GroupLogHom α β) α β where

public instance : IsOneHom (GroupEmbedding α β) α β where
public instance : IsZeroHom (AddGroupEmbedding α β) α β where
public instance : IsExpZeroHom (GroupExpEmbedding α β) α β where
public instance : IsLogOneHom (GroupLogEmbedding α β) α β where
public instance : IsMulHom (GroupEmbedding α β) α β where
public instance : IsAddHom (AddGroupEmbedding α β) α β where
public instance : IsExpHom (GroupExpEmbedding α β) α β where
public instance : IsLogHom (GroupLogEmbedding α β) α β where

public instance : IsOneHom (OneEquiv α β) α β where
public instance : IsZeroHom (ZeroEquiv α β) α β where
public instance : IsExpZeroHom (ExpZeroEquiv α β) α β where
public instance : IsLogOneHom (LogOneEquiv α β) α β where
public instance : IsOneHom (GroupEquiv α β) α β where
public instance : IsZeroHom (AddGroupEquiv α β) α β where
public instance : IsExpZeroHom (GroupExpEquiv α β) α β where
public instance : IsLogOneHom (GroupLogEquiv α β) α β where
public instance : IsMulHom (GroupEquiv α β) α β where
public instance : IsAddHom (AddGroupEquiv α β) α β where
public instance : IsExpHom (GroupExpEquiv α β) α β where
public instance : IsLogHom (GroupLogEquiv α β) α β where

end Impls

section AddMul

public instance [Funlike F α β] [Zero α] [Zero β] [IsZeroHom F α β] : IsOneHom (MulOfAdd F) (MulOfAdd α) (MulOfAdd β) where
  map_one := map_zero (F := F) (α := α) (β := β)
public instance [Funlike F α β] [One α] [One β] [IsOneHom F α β] : IsZeroHom (AddOfMul F) (AddOfMul α) (AddOfMul β) where
  map_zero := map_one (F := F) (α := α) (β := β)

end AddMul

section Theorems.One

variable {α β γ: Type*} [One α] [One β] [One γ]

section Reduction

@[simp] public theorem OneEquiv.apply_toEquiv (f: α ≃₁ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem OneEquiv.apply_toOneHom (f: α ≃₁ β) (x: α) : f.toOneHom x = f x := rfl

@[ext] public theorem OneHom.ext (f g: α →₁ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem OneEquiv.ext (f g: α ≃₁ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def OneHom.id (α: Type*) [One α] : α →₁ α where
  toFun := id
  map_one := rfl
@[expose] public protected def OneEquiv.id (α: Type*) [One α] : α ≃₁ α := {
  Equiv.id _, OneHom.id _ with
}

@[expose] public def OneHom.comp (f: β →₁ γ) (g: α →₁ β) : α →₁ γ where
  toFun := f ∘ g
  map_one := by dsimp only [Function.comp_apply]; rw [map_one, map_one]
@[expose] public def OneEquiv.comp (f: β ≃₁ γ) (g: α ≃₁ β) : α ≃₁ γ := {
  f.toEquiv.comp g.toEquiv, f.toOneHom.comp g.toOneHom with
}
@[expose] public def OneEquiv.trans (f: α ≃₁ β) (g: β ≃₁ γ) : α ≃₁ γ := comp g f
@[expose] public def OneEquiv.symm (f: α ≃₁ β) : β ≃₁ α := {
  f.toEquiv.symm with
  map_one := by
    apply f.inj; dsimp only [Equiv.normalize_toFun, apply_toEquiv]
    rw [map_one f]
    rw [←apply_toEquiv, f.symm_apply]
}

end Api

namespace OneHom

@[simp] public theorem apply_id : OneEquiv.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →₁ γ) (g: α →₁ β) (x: α) : f.comp g x = f (g x) := rfl

end OneHom

namespace OneEquiv

@[simp] public theorem apply_id : OneEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃₁ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃₁ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃₁ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃₁ γ) (g: α ≃₁ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃₁ β) (g: β ≃₁ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃₁ β) : f.symm.comp f = OneEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃₁ β) : f.comp f.symm = OneEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃₁ β) : f.symm.trans f = OneEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃₁ β) : f.trans f.symm = OneEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃₁ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃₁ β) : Function.Surjective f := f.symm.rightInv.surjective

end OneEquiv

end Theorems.One

section Theorems.Zero

variable {α β γ: Type*} [Zero α] [Zero β] [Zero γ]

section Reduction

@[simp] public theorem ZeroEquiv.apply_toEquiv (f: α ≃₀ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem ZeroEquiv.apply_toZeroHom (f: α ≃₀ β) (x: α) : f.toZeroHom x = f x := rfl

@[ext] public theorem ZeroHom.ext (f g: α →₀ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem ZeroEquiv.ext (f g: α ≃₀ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def ZeroHom.id (α: Type*) [Zero α] : α →₀ α where
  toFun := id
  map_zero := rfl
@[expose] public protected def ZeroEquiv.id (α: Type*) [Zero α] : α ≃₀ α := {
  Equiv.id _, ZeroHom.id _ with
}

@[expose] public def ZeroHom.comp (f: β →₀ γ) (g: α →₀ β) : α →₀ γ where
  toFun := f ∘ g
  map_zero := by dsimp only [Function.comp_apply]; rw [map_zero, map_zero]
@[expose] public def ZeroEquiv.comp (f: β ≃₀ γ) (g: α ≃₀ β) : α ≃₀ γ := {
  f.toEquiv.comp g.toEquiv, f.toZeroHom.comp g.toZeroHom with
}
@[expose] public def ZeroEquiv.trans (f: α ≃₀ β) (g: β ≃₀ γ) : α ≃₀ γ := comp g f
@[expose] public def ZeroEquiv.symm (f: α ≃₀ β) : β ≃₀ α := {
  f.toEquiv.symm with
  map_zero := by
    apply f.inj; dsimp only [Equiv.normalize_toFun, apply_toEquiv]
    rw [map_zero f]
    rw [←apply_toEquiv, f.symm_apply]
}

end Api

namespace ZeroHom

@[simp] public theorem apply_id : ZeroEquiv.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →₀ γ) (g: α →₀ β) (x: α) : f.comp g x = f (g x) := rfl

end ZeroHom

namespace ZeroEquiv

@[simp] public theorem apply_id : ZeroEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃₀ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃₀ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃₀ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃₀ γ) (g: α ≃₀ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃₀ β) (g: β ≃₀ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃₀ β) : f.symm.comp f = ZeroEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃₀ β) : f.comp f.symm = ZeroEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃₀ β) : f.symm.trans f = ZeroEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃₀ β) : f.trans f.symm = ZeroEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃₀ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃₀ β) : Function.Surjective f := f.symm.rightInv.surjective

end ZeroEquiv

end Theorems.Zero

section Theorems.Group

variable {α β γ: Type*} [Mul α] [One α] [Mul β] [One β] [Mul γ] [One γ]

section Reduction

@[simp] public theorem GroupEmbedding.apply_toEmbedding (f: α ↪* β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem GroupEquiv.apply_toEquiv (f: α ≃* β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem GroupEmbedding.apply_toGroupHom (f: α ↪* β) (x: α) : f.toGroupHom x = f x := rfl
@[simp] public theorem GroupEquiv.apply_toGroupHom (f: α ≃* β) (x: α) : f.toGroupHom x = f x := rfl

@[ext] public theorem GroupHom.ext (f g: α →* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem GroupEmbedding.ext (f g: α ↪* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem GroupEquiv.ext (f g: α ≃* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public def GroupHom.of
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) : α →* β where
  toFun := f
  map_one := map_one f
  map_mul := map_mul f

@[expose] public def GroupEmbedding.of
  [EmbeddingLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) : α ↪* β where
  toEmbedding := f
  map_one := map_one f
  map_mul := map_mul f

@[expose] public def GroupEquiv.of
  [EquivLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) : α ≃* β where
  toEquiv := f
  map_one := map_one f
  map_mul := map_mul f

@[expose] public def GroupHom.copy
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) : α →* β where
  toFun := g
  map_one := by rw [←h, map_one]
  map_mul a b := by rw [←h, ←h, ←h, map_mul]

@[expose] public protected def GroupHom.id (α: Type*) [Mul α] [One α] : α →* α := {
  MulHom.id α, OneHom.id α with
}
@[expose] public protected def GroupEmbedding.id (α: Type*) [Mul α] [One α] : α ↪* α := {
  Embedding.id _, GroupHom.id _ with
}
@[expose] public protected def GroupEquiv.id (α: Type*) [Mul α] [One α] : α ≃* α := {
  Equiv.id _, GroupHom.id _ with
}

@[expose] public def GroupHom.comp (f: β →* γ) (g: α →* β) : α →* γ := {
  f.toMulHom.comp g.toMulHom, f.toOneHom.comp g.toOneHom with
}
@[expose] public def GroupEmbedding.comp (f: β ↪* γ) (g: α ↪* β) : α ↪* γ := {
  f.toEmbedding.comp g.toEmbedding, f.toGroupHom.comp g.toGroupHom with
}
@[expose] public def GroupEquiv.comp (f: β ≃* γ) (g: α ≃* β) : α ≃* γ := {
  f.toEquiv.comp g.toEquiv, f.toGroupHom.comp g.toGroupHom with
}
@[expose] public def GroupEmbedding.trans (f: α ↪* β) (g: β ↪* γ) : α ↪* γ := comp g f
@[expose] public def GroupEquiv.trans (f: α ≃* β) (g: β ≃* γ) : α ≃* γ := comp g f
@[expose] public def GroupEquiv.symm (f: α ≃* β) : β ≃* α := {
  f.toMulEquiv.symm, f.toOneEquiv.symm with
}

@[expose] public def GroupEquiv.mul_of_add_inv_add_of_mul (α: Type*) [Mul α] [One α] : MulOfAdd (AddOfMul α) ≃* α :=
  GroupEquiv.id α
@[expose] public def GroupEquiv.mul_opp₂ (α: Type*) [Mul α] [One α] : αᵐᵒᵖᵐᵒᵖ ≃* α :=
  GroupEquiv.id α

end Api

namespace GroupHom

@[simp] public theorem apply_of
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : GroupHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →* γ) (g: α →* β) (x: α) : f.comp g x = f (g x) := rfl

end GroupHom

namespace GroupEmbedding

@[simp] public theorem apply_of
  [EmbeddingLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : GroupEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪* γ) (g: α ↪* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪* β) (g: β ↪* γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪* β) : Function.Injective f := f.injective

end GroupEmbedding

namespace GroupEquiv

@[simp] public theorem apply_of
  [EquivLike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : GroupEquiv.id α x = x := rfl

@[simp] public theorem apply_copy
  [Funlike F α β] [IsOneHom F α β] [IsMulHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) (a: α) : GroupHom.copy f g h a = f a := (h a).symm

@[simp] public theorem apply_symm (f: α ≃* β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃* β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃* β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃* γ) (g: α ≃* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃* β) (g: β ≃* γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃* β) : f.symm.comp f = GroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃* β) : f.comp f.symm = GroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃* β) : f.symm.trans f = GroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃* β) : f.trans f.symm = GroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

attribute [local irreducible] AddOfMul MulOfAdd

@[simp] public theorem apply_mul_of_add_inv_add_of_mul (a: MulOfAdd (AddOfMul α)) : GroupEquiv.mul_of_add_inv_add_of_mul α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_mul_of_add_inv_add_of_mul (a: α) : (GroupEquiv.mul_of_add_inv_add_of_mul α).symm a = .mk (.mk a) :=
  rfl

@[simp] public theorem apply_mul_opp₂ (a: αᵐᵒᵖᵐᵒᵖ) : GroupEquiv.mul_opp₂ α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_mul_opp₂ (a: α) : (GroupEquiv.mul_opp₂ α).symm a = .mk (.mk a) :=
  rfl

public theorem inj (f: α ≃* β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃* β) : Function.Surjective f := f.symm.rightInv.surjective

end GroupEquiv

end Theorems.Group

section Theorems.AddGroup

variable {α β γ: Type*} [Add α] [Zero α] [Add β] [Zero β] [Add γ] [Zero γ]

section Reduction

@[simp] public theorem AddGroupEmbedding.apply_toEmbedding (f: α ↪+ β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem AddGroupEquiv.apply_toEquiv (f: α ≃+ β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem AddGroupEmbedding.apply_toAddGroupHom (f: α ↪+ β) (x: α) : f.toAddGroupHom x = f x := rfl
@[simp] public theorem AddGroupEquiv.apply_toAddGroupHom (f: α ≃+ β) (x: α) : f.toAddGroupHom x = f x := rfl

@[ext] public theorem AddGroupHom.ext (f g: α →+ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddGroupEmbedding.ext (f g: α ↪+ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem AddGroupEquiv.ext (f g: α ≃+ β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public def AddGroupHom.of
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) : α →+ β where
  toFun := f
  map_zero := map_zero f
  map_add := map_add f

@[expose] public def AddGroupEmbedding.of
  [EmbeddingLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) : α ↪+ β where
  toEmbedding := f
  map_zero := map_zero f
  map_add := map_add f

@[expose] public def AddGroupEquiv.of
  [EquivLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) : α ≃+ β where
  toEquiv := f
  map_zero := map_zero f
  map_add := map_add f

@[expose] public def AddGroupHom.copy
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) : α →+ β where
  toFun := g
  map_zero := by rw [←h, map_zero]
  map_add a b := by rw [←h, ←h, ←h, map_add]

@[expose] public protected def AddGroupHom.id (α: Type*) [Add α] [Zero α] : α →+ α := {
  AddHom.id α, ZeroHom.id α with
}
@[expose] public protected def AddGroupEmbedding.id (α: Type*) [Add α] [Zero α] : α ↪+ α := {
  Embedding.id _, AddGroupHom.id _ with
}
@[expose] public protected def AddGroupEquiv.id (α: Type*) [Add α] [Zero α] : α ≃+ α := {
  Equiv.id _, AddGroupHom.id _ with
}

@[expose] public def AddGroupHom.comp (f: β →+ γ) (g: α →+ β) : α →+ γ := {
  f.toAddHom.comp g.toAddHom, f.toZeroHom.comp g.toZeroHom with
}
@[expose] public def AddGroupEmbedding.comp (f: β ↪+ γ) (g: α ↪+ β) : α ↪+ γ := {
  f.toEmbedding.comp g.toEmbedding, f.toAddGroupHom.comp g.toAddGroupHom with
}
@[expose] public def AddGroupEquiv.comp (f: β ≃+ γ) (g: α ≃+ β) : α ≃+ γ := {
  f.toEquiv.comp g.toEquiv, f.toAddGroupHom.comp g.toAddGroupHom with
}
@[expose] public def AddGroupEmbedding.trans (f: α ↪+ β) (g: β ↪+ γ) : α ↪+ γ := comp g f
@[expose] public def AddGroupEquiv.trans (f: α ≃+ β) (g: β ≃+ γ) : α ≃+ γ := comp g f
@[expose] public def AddGroupEquiv.symm (f: α ≃+ β) : β ≃+ α := {
  f.toAddEquiv.symm, f.toZeroEquiv.symm with
}

@[expose] public def AddGroupEquiv.add_of_mul_inv_mul_of_add (α: Type*) [Add α] [Zero α] : AddOfMul (MulOfAdd α) ≃+ α :=
  AddGroupEquiv.id α
@[expose] public def AddGroupEquiv.add_opp₂ (α: Type*) [Add α] [Zero α] : αᵃᵒᵖᵃᵒᵖ ≃+ α :=
  AddGroupEquiv.id α

end Api

namespace AddGroupHom

@[simp] public theorem apply_of
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_copy
  [Funlike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (g: α -> β) (h: ∀i, f i = g i) (a: α) : copy f g h a = f a := (h a).symm

@[simp] public theorem apply_id : AddGroupHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →+ γ) (g: α →+ β) (x: α) : f.comp g x = f (g x) := rfl

end AddGroupHom

namespace AddGroupEmbedding

@[simp] public theorem apply_of
  [EmbeddingLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : AddGroupEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪+ γ) (g: α ↪+ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪+ β) (g: β ↪+ γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪+ β) : Function.Injective f := f.injective

end AddGroupEmbedding

namespace AddGroupEquiv

@[simp] public theorem apply_of
  [EquivLike F α β] [IsZeroHom F α β] [IsAddHom F α β]
  (f: F) (a: α) : of f a = f a := rfl

@[simp] public theorem apply_id : AddGroupEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃+ β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃+ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃+ β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃+ γ) (g: α ≃+ β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃+ β) (g: β ≃+ γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃+ β) : f.symm.comp f = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃+ β) : f.comp f.symm = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃+ β) : f.symm.trans f = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃+ β) : f.trans f.symm = AddGroupEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

attribute [local irreducible] AddOfMul MulOfAdd

@[simp] public theorem apply_add_of_mul_inv_mul_of_add (a: AddOfMul (MulOfAdd α)) : AddGroupEquiv.add_of_mul_inv_mul_of_add α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_add_of_mul_inv_mul_of_add (a: α) : (AddGroupEquiv.add_of_mul_inv_mul_of_add α).symm a = .mk (.mk a) :=
  rfl

@[simp] public theorem apply_mul_opp₂ (a: αᵃᵒᵖᵃᵒᵖ) : add_opp₂ α a = a.get.get :=
  rfl
@[simp] public theorem symm_apply_mul_opp₂ (a: α) : (add_opp₂ α).symm a = .mk (.mk a) :=
  rfl

public theorem inj (f: α ≃+ β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃+ β) : Function.Surjective f := f.symm.rightInv.surjective

end AddGroupEquiv

end Theorems.AddGroup

end Hom

section Basic

public instance [AddMonoidOps α] [IsLawfulNSMul α] : IsLawfulPowN (MulOfAdd α) where
  pown_zero := zero_nsmul (α := α)
  pown_succ := succ_nsmul (α := α)
public instance [MonoidOps α] [IsLawfulPowN α] : IsLawfulNSMul (AddOfMul α) where
  zero_nsmul := pown_zero (α := α)
  succ_nsmul := pown_succ (α := α)
public instance [MonoidOps α] [IsMonoid α] : IsAddMonoid (AddOfMul α) where
public instance [AddMonoidOps α] [IsAddMonoid α] : IsMonoid (MulOfAdd α) where

public instance : IsLawfulZeroMul ℕ where
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
public instance : IsLawfulZeroMul ℤ where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
public instance : IsLawfulOne ℕ where
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
public instance : IsLawfulOne ℤ where
  one_mul := Int.one_mul
  mul_one := Int.mul_one
public instance : IsLawfulZero ℕ where
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
public instance : IsLawfulZero ℤ where
  zero_add := Int.zero_add
  add_zero := Int.add_zero
public instance : NoZeroDivisors ℕ := inferInstance
public instance : NoZeroDivisors ℤ := inferInstance

public instance : IsAddMonoid ℕ where
  zero_nsmul := Nat.zero_mul
  succ_nsmul n m := Nat.succ_mul m n
public instance : IsMonoid ℕ where
  pown_zero _ := rfl
  pown_succ _ _ := rfl
public instance : IsAddMonoid ℤ where
  zero_nsmul := Int.zero_mul
  succ_nsmul n m := by
    show (m + 1: ℤ) * n = m * n + n
    rw [Int.add_mul, one_mul]
public instance : IsMonoid ℤ where
  pown_zero := Int.pow_zero
  pown_succ := Int.pow_succ

end Basic

section Theorems

public theorem subingleton_of_zero_eq_one (α: Type*) [Zero α] [One α] [Mul α] [IsLawfulZeroMul α] [IsLawfulOne α] (h: (0: α) = (1: α)) : Subsingleton α where
  allEq a b := by
    rw [←one_mul a, ←one_mul b, ←h, zero_mul, zero_mul]

public instance
  (priority := 100)
  [Nontrivial α] [Zero α] [One α] [Mul α]
  [IsLawfulOne α] [IsLawfulZeroMul α]
  [∀a: α, ExcludedMiddle (1 = a)] : IsZeroNeOne α where
  zero_ne_one := by
    intro h
    have ⟨b, g⟩ := Nontrivial.exists_ne (1: α)
    rw [←mul_one b, ←h, mul_zero] at g
    contradiction

public instance [Zero α] [One α] [IsZeroNeOne α] : Nontrivial α := .intro 0 1 zero_ne_one

macro_rules
| `(tactic|contradiction) => `(tactic|nomatch zero_ne_one _ (by assumption))
macro_rules
| `(tactic|contradiction) => `(tactic|nomatch zero_ne_one _ (Eq.symm (by assumption)))

public theorem map_pown [Funlike F α β]
  [MonoidOps α] [MonoidOps β]
  [IsLawfulPowN α] [IsLawfulPowN β]
  [IsMulHom F α β] [IsOneHom F α β]
  (f: F) (a: α) (n: ℕ) : f (a ^ n) = f a ^ n := by
  induction n with
  | zero => rw [pown_zero, pown_zero, map_one]
  | succ n ih => rw [pown_succ, pown_succ, map_mul, ih]

public theorem map_nsmul [Funlike F α β]
  [AddMonoidOps α] [AddMonoidOps β]
  [IsLawfulNSMul α] [IsLawfulNSMul β]
  [IsAddHom F α β] [IsZeroHom F α β]
  (f: F) (a: α) (n: ℕ) : f (n • a) = n • f a :=
  map_pown (MulOfAdd.mk f) (MulOfAdd.mk a) n

public theorem smul_eq_mul [Mul α] (a b: α) : a • b = a * b := rfl

public instance [MonoidOps α] [IsMonoid α] (a b: α) [IsCommAt a b] (n: ℕ) : IsCommAt a (b ^ n) where
  mul_comm := by
    induction n with
    | zero => rw [pown_zero, mul_one, one_mul]
    | succ n ih => rw [pown_succ, ←mul_assoc, ih, mul_assoc, mul_assoc, mul_comm a]

public instance [AddMonoidOps α] [IsAddMonoid α] (a b: α) [IsAddCommAt a b] (n: ℕ) : IsAddCommAt a (n • b) where
  add_comm := mul_comm (MulOfAdd.mk a) (MulOfAdd.mk b ^ n)

public theorem pown_succ_left [MonoidOps α] [IsMonoid α] (a: α) (n: ℕ) : a ^ (n + 1) = a * a ^ n := by
  rw [mul_comm a, pown_succ]

public theorem succ_nsmul_left [AddMonoidOps α] [IsAddMonoid α] (a: α) (n: ℕ) : (n + 1) • a = a + n • a :=
  pown_succ_left (α := MulOfAdd α) a n

@[expose] public def nsmul_hom [AddMonoidOps α] [IsAddMonoid α] (a: α) : ℕ →+ α where
  toFun n := n • a
  map_zero := by rw [zero_nsmul]
  map_add n m := by
    induction m with
    | zero => rw [add_zero, zero_nsmul, add_zero]
    | succ m ih => rw [Nat.add_succ, succ_nsmul, succ_nsmul, ←add_assoc, ih]

@[expose] public def pown_hom [MonoidOps α] [IsMonoid α] (a: α) : ℕ →ₘ+ α where
  toFun n := a ^ n
  map_zero_to_one := map_zero (β := AddOfMul α) (nsmul_hom (AddOfMul.mk a))
  map_add_to_mul := map_add (β := AddOfMul α) (nsmul_hom (AddOfMul.mk a))

public theorem mul_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) (n m: ℕ) : (n * m) • a = n • m • a := by
  rw [←smul_eq_mul n m]
  show nsmul_hom a (n • m) = n • nsmul_hom a m
  rw [map_nsmul]

public theorem pown_mul [MonoidOps α] [IsMonoid α] (a: α) (n m: ℕ) : a ^ (n * m) = (a ^ m) ^ n :=
  mul_nsmul (α := AddOfMul α) a n m

public theorem add_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) (n m: ℕ) : (n + m) • a = n • a + m • a :=
  map_add (nsmul_hom a) _ _

public theorem pown_add [MonoidOps α] [IsMonoid α] (a: α) (n m: ℕ) : a ^ (n + m) = a ^ n * a ^ m :=
  add_nsmul (α := AddOfMul α) a n m

public theorem nsmul_add [AddMonoidOps α] [IsAddMonoid α] (a b: α) [IsAddCommAt a b] (n: ℕ) : n • (a + b) = n • a + n • b := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, add_zero]
  | succ n ih =>
    iterate 3 rw [succ_nsmul]
    rw [ih, add_assoc, ←add_assoc _ a, add_comm _ a, add_assoc a, ←add_assoc _ a]

public theorem mul_pown [MonoidOps α] [IsMonoid α] (a b: α) [IsCommAt a b] (n: ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
  nsmul_add (α := AddOfMul α) (AddOfMul.mk a) (AddOfMul.mk b) n

public theorem nsmul_zero [AddMonoidOps α] [IsAddMonoid α] (n: ℕ) : n • (0: α) = 0 := by
  induction n with
  | zero => rw [zero_nsmul]
  | succ n ih => rw [succ_nsmul, add_zero, ih]
public theorem one_pown [MonoidOps α] [IsMonoid α] (n: ℕ) : (1: α) ^ n = 1 :=
  nsmul_zero (α := AddOfMul α) n

public theorem one_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) : 1 • a = a := by
  rw [succ_nsmul, zero_nsmul, zero_add]
public theorem pown_one [MonoidOps α] [IsMonoid α] (a: α) : a ^ 1 = a :=
  one_nsmul (α := AddOfMul α) a
public theorem two_nsmul [AddMonoidOps α] [IsAddMonoid α] (a: α) : 2 • a = a + a := by
  rw [succ_nsmul, one_nsmul]
public theorem pown_two [MonoidOps α] [IsMonoid α] (a: α) : a ^ 2 = a * a :=
  two_nsmul (α := AddOfMul α) _

end Theorems

section Opp

public instance [Mul α] [One α] [IsLawfulOne α] : IsLawfulOne αᵐᵒᵖ where
  one_mul := mul_one (α := α)
  mul_one := one_mul (α := α)
public instance [Add α] [Zero α] [IsLawfulZero α] : IsLawfulZero αᵃᵒᵖ where
  zero_add := add_zero (α := α)
  add_zero := zero_add (α := α)
public instance [MonoidOps α] [IsMonoid α] : IsLawfulPowN αᵐᵒᵖ where
  pown_zero := pown_zero (α := α)
  pown_succ := pown_succ_left (α := α)
public instance [AddMonoidOps α] [IsAddMonoid α] : IsLawfulNSMul αᵃᵒᵖ where
  zero_nsmul := zero_nsmul (α := α)
  succ_nsmul := succ_nsmul_left (α := α)
public instance [MonoidOps α] [IsMonoid α] : IsMonoid αᵐᵒᵖ where
public instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid αᵃᵒᵖ where

end Opp

public instance : IsZeroNeOne ℕ := inferInstance
public instance : IsZeroNeOne ℤ := inferInstance

namespace OfEquiv

variable (f: α ≃ β)

public instance [Mul α] [One α] [Pow α ℕ] [IsLawfulPowN α] : IsLawfulPowN (OfEquiv f) where
  pown_zero a := by
    induction a with | _ a =>
    simp; rw [pown_zero]
  pown_succ a n := by
    induction a with | _ a =>
    simp; rw [pown_succ]
public instance [Add α] [Zero α] [SMul ℕ α] [IsLawfulNSMul α] : IsLawfulNSMul (OfEquiv f) where
  zero_nsmul a := by
    induction a with | _ a =>
    simp; rw [zero_nsmul]
  succ_nsmul a n := by
    induction a with | _ a =>
    simp; rw [succ_nsmul]
public instance [Mul α] [One α] [IsLawfulOne α] : IsLawfulOne (OfEquiv f) where
  mul_one a := by
    induction a with | _ a =>
    simp; rw [mul_one]
  one_mul a := by
    induction a with | _ a =>
    simp; rw [one_mul]
public instance [Mul α] [Zero α] [IsLawfulZeroMul α] : IsLawfulZeroMul (OfEquiv f) where
  mul_zero a := by
    induction a with | _ a =>
    simp; rw [mul_zero]
  zero_mul a := by
    induction a with | _ a =>
    simp; rw [zero_mul]
public instance [Add α] [Zero α] [IsLawfulZero α] : IsLawfulZero (OfEquiv f) where
  add_zero a := by
    induction a with | _ a =>
    simp; rw [add_zero]
  zero_add a := by
    induction a with | _ a =>
    simp; rw [zero_add]
public instance [MonoidOps α] [IsMonoid α] : IsMonoid (OfEquiv f) where
public instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (OfEquiv f) where

end OfEquiv

namespace GroupHom

variable {α β: Type*} [One α] [Mul α] [MonoidOps β] [IsMonoid β]

public instance : One (GroupHom α β) where
  one := {
    toFun _ := 1
    map_one := rfl
    map_mul _ _ := (mul_one _).symm
  }

public instance [IsComm β] : Mul (GroupHom α β) where
  mul a b := {
    toFun i := a i * b i
    map_one := by rw [map_one, map_one, mul_one]
    map_mul i j := by
      rw [map_mul, map_mul, mul_assoc, ←mul_assoc (a j), mul_comm (a j),
        ←mul_assoc, ←mul_assoc, mul_assoc (_ * _)]
  }

public instance [IsComm β] : Pow (GroupHom α β) ℕ where
  pow a n := {
    toFun i := a i ^ n
    map_one := by rw [map_one, one_pown]
    map_mul i j := by rw [map_mul, mul_pown]
  }

public instance [IsComm β] : IsMonoid (GroupHom α β) where
  mul_assoc _ _ _ := by ext; apply mul_assoc
  mul_one _ := by ext; apply mul_one
  one_mul _ := by ext; apply one_mul
  pown_zero _ := by ext; apply pown_zero
  pown_succ _ _ := by ext; apply pown_succ

public instance [IsComm β] : IsComm (GroupHom α β) where
  mul_comm _ _ := by ext; apply mul_comm

end GroupHom

namespace AddGroupHom

variable {α β: Type*} [Zero α] [Add α] [AddMonoidOps β] [IsAddMonoid β]

public instance : Zero (AddGroupHom α β) where
  zero := {
    toFun _ := 0
    map_zero := rfl
    map_add _ _ := (add_zero _).symm
  }

public instance [IsAddComm β] : Add (AddGroupHom α β) where
  add a b := {
    toFun i := a i + b i
    map_zero := by rw [map_zero, map_zero, add_zero]
    map_add i j := by
      rw [map_add, map_add, add_assoc, ←add_assoc (a j), add_comm (a j),
        ←add_assoc, ←add_assoc, add_assoc (_ + _)]
  }

public instance [IsAddComm β] : SMul ℕ (AddGroupHom α β) where
  smul n a := {
    toFun i := n • a i
    map_zero := by rw [map_zero, nsmul_zero]
    map_add i j := by rw [map_add, nsmul_add]
  }

public instance [IsAddComm β] : IsAddMonoid (AddGroupHom α β) where
  add_assoc _ _ _ := by ext; apply add_assoc
  add_zero _ := by ext; apply add_zero
  zero_add _ := by ext; apply zero_add
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul

public instance [IsAddComm β] : IsAddComm (AddGroupHom α β) where
  add_comm _ _ := by ext; apply add_comm

@[simp] public theorem apply_zero (i: α) : (0: α →+ β) i = 0 := rfl
@[simp] public theorem apply_add [IsAddComm β] (a b: α →+ β) (i: α) : (a + b) i = a i + b i := rfl
@[simp] public theorem apply_nsul [IsAddComm β] (n: ℕ) (a: α →+ β) (i: α) : (n • a) i = n • a i := rfl

end AddGroupHom
