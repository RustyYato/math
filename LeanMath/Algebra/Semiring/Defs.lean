import LeanMath.Algebra.AddMonoidWithOne.Defs
import LeanMath.Algebra.MonoidWithZero.Defs

class SemiringOps (α: Type*) extends AddMonoidWithOneOps α, MonoidOps α where

instance (priority := 900) [AddMonoidWithOneOps α] [MonoidOps α] : SemiringOps α where

class IsLeftDistrib (α: Type*) [Mul α] [Add α] : Prop where
  protected mul_add (k a b: α) : k * (a + b) = k * a + k * b

class IsRightDistrib (α: Type*) [Mul α] [Add α] : Prop where
  protected add_mul (a b k: α) : (a + b) * k = a * k + b * k

def mul_add [Mul α] [Add α] [IsLeftDistrib α] (k a b: α) : k * (a + b) = k * a + k * b :=
  IsLeftDistrib.mul_add _ _ _

def add_mul [Mul α] [Add α] [IsRightDistrib α] (a b k: α) : (a + b) * k = a * k + b * k :=
  IsRightDistrib.add_mul _ _ _

instance (priority := 100) [Mul α] [Add α] [IsComm α] [IsLeftDistrib α]
  : IsRightDistrib α where
  add_mul a b k := by
    repeat rw [mul_comm _ k]
    rw [mul_add]
instance (priority := 100) [Mul α] [Add α] [IsComm α] [IsRightDistrib α]
  : IsLeftDistrib α where
  mul_add k a b := by
    repeat rw [mul_comm k]
    rw [add_mul]

class IsNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] extends IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsLawfulZeroMul α, IsAddComm α  where

class IsNonUnitalSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsSemigroup α where

class IsNonAssocSemiring (α: Type*)
  [AddMonoidWithOneOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsAddMonoidWithOne α, IsLawfulOneMul α where

class IsSemiring (α: Type*) [SemiringOps α] : Prop extends IsNonUnitalSemiring α, IsNonAssocSemiring α, IsMonoidWithZero α where

section

structure NonUnitalRingHom (α β: Type*)
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] extends AddGroupHom α β, MulHom α β where

structure NonUnitalRingEmbedding (α β: Type*)
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] extends α ↪ β, NonUnitalRingHom α β, α ↪+ β, α ↪*ₙ β where

structure NonUnitalRingEquiv (α β: Type*)
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] extends α ≃ β, NonUnitalRingHom α β, α ≃+ β, α ≃*ₙ β where

structure RingHom (α β: Type*)
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] [One α] [One β] extends Hom α β, MulHom α β, AddHom α β, α →₀ β, α →₁ β, α →* β, α →+ β, α →+₁ β, NonUnitalRingHom α β where

structure RingEmbedding (α β: Type*)
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] [One α] [One β] extends α ↪ β, RingHom α β, α ↪+ β, α ↪* β, NonUnitalRingEmbedding α β where

structure RingEquiv (α β: Type*)
  [Add α] [Add β] [Zero α] [Zero β]
  [Mul α] [Mul β] [One α] [One β] extends α ≃ β, RingHom α β, α ≃+ β, α ≃* β, NonUnitalRingEquiv α β where

infixr:80 " →+*₀ " => NonUnitalRingHom
infixr:80 " ↪+*₀ " => NonUnitalRingEmbedding
infixr:80 " ≃+*₀ " => NonUnitalRingEquiv

infixr:80 " →+* " => RingHom
infixr:80 " ↪+* " => RingEmbedding
infixr:80 " ≃+* " => RingEquiv

variable
  [Add α] [Add β] [Add γ] [Zero α] [Zero β] [Zero γ]
  [Mul α] [Mul β] [Mul γ] [One α] [One β] [One γ]

instance (priority := 10000) : FunLike (α →+*₀ β) α β where
instance (priority := 10000) : IsZeroHom (α →+*₀ β) α β where
instance (priority := 10000) : IsAddHom (α →+*₀ β) α β where
instance (priority := 10000) : IsMulHom (α →+*₀ β) α β where

instance (priority := 10000) : EmbeddingLike (α ↪+*₀ β) α β where
instance (priority := 10000) : IsZeroHom (α ↪+*₀ β) α β where
instance (priority := 10000) : IsAddHom (α ↪+*₀ β) α β where
instance (priority := 10000) : IsMulHom (α ↪+*₀ β) α β where

instance (priority := 10000) : EquivLike (α ≃+*₀ β) α β where
instance (priority := 10000) : IsZeroHom (α ≃+*₀ β) α β where
instance (priority := 10000) : IsAddHom (α ≃+*₀ β) α β where
instance (priority := 10000) : IsMulHom (α ≃+*₀ β) α β where

instance (priority := 10000) : FunLike (α →+* β) α β where
instance (priority := 10000) : IsZeroHom (α →+* β) α β where
instance (priority := 10000) : IsAddHom (α →+* β) α β where
instance (priority := 10000) : IsOneHom (α →+* β) α β where
instance (priority := 10000) : IsMulHom (α →+* β) α β where

instance (priority := 10000) : EmbeddingLike (α ↪+* β) α β where
instance (priority := 10000) : IsZeroHom (α ↪+* β) α β where
instance (priority := 10000) : IsAddHom (α ↪+* β) α β where
instance (priority := 10000) : IsOneHom (α ↪+* β) α β where
instance (priority := 10000) : IsMulHom (α ↪+* β) α β where

instance (priority := 10000) : EquivLike (α ≃+* β) α β where
instance (priority := 10000) : IsZeroHom (α ≃+* β) α β where
instance (priority := 10000) : IsAddHom (α ≃+* β) α β where
instance (priority := 10000) : IsOneHom (α ≃+* β) α β where
instance (priority := 10000) : IsMulHom (α ≃+* β) α β where

@[ext]
def RingHom.ext (f g: α →+* β) (h: ∀x, f x = g x) : f = g := DFunLike.ext f g h

@[simp] def RingHom.apply_mk (f: α -> β) (h₀ h₁ h₂ h₃) : ({ toFun := f,  map_zero := h₀, map_one := h₁, map_add := h₂, map_mul := h₃ }: α →+* β) a = f a := rfl

def NonUnitalRingEmbedding.comp (f: β ↪+*₀ γ) (g: α ↪+*₀ β) : α ↪+*₀ γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_zero := map_zero <| f.toZeroEmbedding.comp g.toZeroEmbedding
  map_add := map_add <| f.toAddEmbedding.comp g.toAddEmbedding
  map_mul := map_mul <| f.toMulEmbedding.comp g.toMulEmbedding
def NonUnitalRingEmbedding.trans (g: α ↪+*₀ β) (f: β ↪+*₀ γ) : α ↪+*₀ γ := f.comp g

def NonUnitalRingHom.comp (f: β →+*₀ γ) (g: α →+*₀ β) : α →+*₀ γ where
  toFun := f ∘ g
  map_zero := map_zero <| f.toZeroHom.comp g.toZeroHom
  map_add := map_add <| f.toAddHom.comp g.toAddHom
  map_mul := map_mul <| f.toMulHom.comp g.toMulHom

def NonUnitalRingEquiv.comp (f: β ≃+*₀ γ) (g: α ≃+*₀ β) : α ≃+*₀ γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_zero := map_zero <| f.toZeroEquiv.comp g.toZeroEquiv
  map_add := map_add <| f.toAddEquiv.comp g.toAddEquiv
  map_mul := map_mul <| f.toMulEquiv.comp g.toMulEquiv
def NonUnitalRingEquiv.trans (g: α ≃+*₀ β) (f: β ≃+*₀ γ) : α ≃+*₀ γ := f.comp g
def NonUnitalRingEquiv.symm (f: α ≃+*₀ β) : β ≃+*₀ α where
  toEquiv := f.toEquiv.symm
  map_zero := map_zero f.toZeroEquiv.symm
  map_add := map_add f.toAddEquiv.symm
  map_mul := map_mul f.toMulEquiv.symm

@[simp] def NonUnitalRingHom.apply_comp (f: β →+*₀ γ) (g: α →+*₀ β) : (f.comp g) x = f (g x) := rfl

@[simp] def NonUnitalRingEmbedding.apply_comp (f: β ↪+*₀ γ) (g: α ↪+*₀ β) : (f.comp g) x = f (g x) := rfl
@[simp] def NonUnitalRingEmbedding.apply_trans (g: α ↪+*₀ β) (f: β ↪+*₀ γ) : (g.trans f) x = f (g x) := rfl

@[simp] def NonUnitalRingEquiv.apply_comp (f: β ≃+*₀ γ) (g: α ≃+*₀ β) : (f.comp g) x = f (g x) := rfl
@[simp] def NonUnitalRingEquiv.apply_trans (g: α ≃+*₀ β) (f: β ≃+*₀ γ) : (g.trans f) x = f (g x) := rfl

@[simp] def NonUnitalRingEquiv.coe_symm (f: α ≃+*₀ β) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def NonUnitalRingEquiv.symm_coe (f: α ≃+*₀ β) : f (f.symm x) = x := Equiv.symm_coe _ _

def NonUnitalRingEmbedding.refl (α: Type*) [Zero α] [One α] [Add α] [Mul α] : α ↪+*₀ α where
  toEmbedding := Embedding.id _
  map_zero := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def NonUnitalRingEquiv.refl (α: Type*) [Zero α] [One α] [Add α] [Mul α] : α ≃+*₀ α where
  toEquiv := Equiv.id _
  map_zero := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

@[simp] def NonUnitalRingEmbedding.apply_refl (x: α) : NonUnitalRingEmbedding.refl _ x = x := rfl
@[simp] def NonUnitalRingEquiv.apply_refl (x: α) : NonUnitalRingEquiv.refl _ x = x := rfl

def RingEmbedding.comp (f: β ↪+* γ) (g: α ↪+* β) : α ↪+* γ where
  toEmbedding := f.toEmbedding.comp g.toEmbedding
  map_zero := map_zero <| f.toZeroEmbedding.comp g.toZeroEmbedding
  map_one := map_one <| f.toOneEmbedding.comp g.toOneEmbedding
  map_add := map_add <| f.toAddEmbedding.comp g.toAddEmbedding
  map_mul := map_mul <| f.toMulEmbedding.comp g.toMulEmbedding
def RingEmbedding.trans (g: α ↪+* β) (f: β ↪+* γ) : α ↪+* γ := f.comp g

def RingHom.comp (f: β →+* γ) (g: α →+* β) : α →+* γ where
  toFun := f ∘ g
  map_zero := map_zero <| f.toZeroHom.comp g.toZeroHom
  map_one := map_one <| f.toOneHom.comp g.toOneHom
  map_add := map_add <| f.toAddHom.comp g.toAddHom
  map_mul := map_mul <| f.toMulHom.comp g.toMulHom

def RingEquiv.comp (f: β ≃+* γ) (g: α ≃+* β) : α ≃+* γ where
  toEquiv := f.toEquiv.comp g.toEquiv
  map_zero := map_zero <| f.toZeroEquiv.comp g.toZeroEquiv
  map_one := map_one <| f.toOneEquiv.comp g.toOneEquiv
  map_add := map_add <| f.toAddEquiv.comp g.toAddEquiv
  map_mul := map_mul <| f.toMulEquiv.comp g.toMulEquiv
def RingEquiv.trans (g: α ≃+* β) (f: β ≃+* γ) : α ≃+* γ := f.comp g
def RingEquiv.symm (f: α ≃+* β) : β ≃+* α where
  toEquiv := f.toEquiv.symm
  map_zero := map_zero f.toZeroEquiv.symm
  map_one := map_one f.toOneEquiv.symm
  map_add := map_add f.toAddEquiv.symm
  map_mul := map_mul f.toMulEquiv.symm

@[simp] def RingHom.apply_comp (f: β →+* γ) (g: α →+* β) : (f.comp g) x = f (g x) := rfl

@[simp] def RingEmbedding.apply_comp (f: β ↪+* γ) (g: α ↪+* β) : (f.comp g) x = f (g x) := rfl
@[simp] def RingEmbedding.apply_trans (g: α ↪+* β) (f: β ↪+* γ) : (g.trans f) x = f (g x) := rfl

@[simp] def RingEquiv.apply_comp (f: β ≃+* γ) (g: α ≃+* β) : (f.comp g) x = f (g x) := rfl
@[simp] def RingEquiv.apply_trans (g: α ≃+* β) (f: β ≃+* γ) : (g.trans f) x = f (g x) := rfl

@[simp] def RingEquiv.coe_symm (f: α ≃+* β) : f.symm (f x) = x := Equiv.coe_symm _ _
@[simp] def RingEquiv.symm_coe (f: α ≃+* β) : f (f.symm x) = x := Equiv.symm_coe _ _

def RingEmbedding.refl (α: Type*) [Zero α] [One α] [Add α] [Mul α] : α ↪+* α where
  toEmbedding := Embedding.id _
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def RingEquiv.refl (α: Type*) [Zero α] [One α] [Add α] [Mul α] : α ≃+* α where
  toEquiv := Equiv.id _
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

@[simp] def RingEmbedding.apply_refl (x: α) : RingEmbedding.refl _ x = x := rfl
@[simp] def RingEquiv.apply_refl (x: α) : RingEquiv.refl _ x = x := rfl

end

section

variable [SemiringOps α] [IsSemiring α] [SemiringOps β] [IsSemiring β]
  [FunLike F α β] [IsZeroHom F α β] [IsOneHom F α β] [IsAddHom F α β] [IsMulHom F α β]

def nsmul_eq_natCast_mul (n: ℕ) (a: α) : n • a = n * a := by
  induction n with
  | zero => rw [natCast_zero, zero_mul, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, add_mul, one_mul, ih]

def nsmul_eq_mul_natCast (n: ℕ) (a: α) : n • a = a * n := by
  induction n with
  | zero => rw [natCast_zero, mul_zero, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, mul_add, mul_one, ih]

instance (n: ℕ) (a: α) : IsCommAt (n: α) a where
  mul_comm := by rw [←nsmul_eq_mul_natCast, ←nsmul_eq_natCast_mul]

instance (n: ℕ) (a: α) : IsCommAt a (n: α) := inferInstance

def natCast_mul (n m: ℕ) : (n * m: ℕ) = (n: α) * m := by
  rw [natCast_eq_nsmul_one, mul_nsmul, ←natCast_eq_nsmul_one,
    nsmul_eq_natCast_mul, mul_comm]

def natCastHom : ℕ →+* α := {
  natCastHom₀ with
  map_mul := natCast_mul
}

@[simp] def apply_natCastHom (n: ℕ) : natCastHom n = (n: α) := rfl

instance : Subsingleton (ℕ →+* α) where
  allEq := by
    suffices ∀f: ℕ →+* α, f = natCastHom by
      intro a b; rw [this a, this b]
    intro f; apply DFunLike.ext; intro z
    show f (Nat.cast z) = _
    rw [map_natCast]
    rfl

def natCast_npow (n m: ℕ) : (n ^ m: ℕ) = (n: α) ^ m :=
  map_npow (f := natCastHom) _ _

def two_mul (a: α) : (2: ℕ) * a = a + a := by
  rw [←nsmul_eq_natCast_mul, succ_nsmul, one_nsmul]

def add_sq (a b: α) [IsCommAt a b] : (a + b) ^ 2 = a ^ 2 + (2: ℕ) * (a * b) + b ^ 2 := by
  rw [npow_succ, npow_one, mul_add, add_mul, add_mul, mul_comm b,
    ←add_assoc, add_assoc (a * a), ←two_mul, ←npow_two, ←npow_two]

end

section

variable [Add α] [Mul α]

variable [RelLike R α] [IsCon R] [IsAddCon R] [IsMulCon R] (r: R)

instance [IsLeftDistrib α] : IsLeftDistrib (AlgQuot r) where
  mul_add k a b := by
    induction k using AlgQuot.ind with | _ k =>
    induction a using AlgQuot.ind with | _ a =>
    induction b using AlgQuot.ind with | _ b =>
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [mul_add]

instance [IsRightDistrib α] : IsRightDistrib (AlgQuot r) where
  add_mul a b k := by
    induction k using AlgQuot.ind with | _ k =>
    induction a using AlgQuot.ind with | _ a =>
    induction b using AlgQuot.ind with | _ b =>
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [add_mul]

end

section

variable [RelLike R α] [IsCon R] (r: R)

instance [SemiringOps α] [IsLawfulPowN α] [IsAddMonoidWithOne α] [IsAddCon R] [IsMulCon R] : SemiringOps (AlgQuot r) := inferInstance

variable [SemiringOps α] [IsSemiring α] [IsAddCon R] [IsMulCon R]

instance : IsSemiring (AlgQuot r) where

end

namespace AlgQuot

variable
  [RelLike R α] [AddMonoidOps α] [MonoidOps α] [IsAddMonoid α] [IsMonoid α] [IsAddCon R] [IsMulCon R]
  [RelLike S β] [AddMonoidOps β] [MonoidOps β] [IsAddMonoid β] [IsMonoid β] [IsAddCon S] [IsMulCon S]
  {r: R} {s: S}

def MkHom.toRingHom (_: MkHom r) : α →+* AlgQuot r where
  toFun := AlgQuot.mk r
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

def liftRingHom : { f: α →+* β // ∀a b, r a b -> f a = f b } ≃ AlgQuot r →+* β where
  toFun f := {
    toFun := Quotient.lift f.val f.property
    map_zero := map_zero f.val
    map_one := map_one f.val
    map_add a b := by
      induction a with | _ a =>
      induction b with | _ b =>
      exact map_add f.val _ _
    map_mul a b := by
      induction a with | _ a =>
      induction b with | _ b =>
      exact map_mul f.val _ _
  }
  invFun f := {
    val := {
      toFun a := f (AlgQuot.mk r a)
      map_zero := map_zero f
      map_one := map_one f
      map_add _ _ := by rw [map_add, map_add]
      map_mul _ _ := by rw [map_mul, map_mul]
    }
    property := by
      intro a b h; dsimp
      rw [AlgQuot.sound _ _ _ h]
  }
  leftInv x := by
    ext a; induction a with | mk a =>
    rfl
  rightInv x := by
    ext a; rfl

@[simp] def mk_liftRingHom (f: { f: α →+* β // ∀a b, r a b -> f a = f b }): liftRingHom f (mk r a) = f.val a := rfl

@[simp] def apply_mkHom_toRingHom : MkHom.toRingHom f x = AlgQuot.mk r x := rfl

def mapRingHom (f: α →+* β) (h: ∀x y, r x y -> s (f x) (f y)) : AlgQuot r →+* AlgQuot s :=
  liftRingHom (r := r) (β := AlgQuot s) {
    val := (AlgQuot.mk s).toRingHom.comp f
    property := by
      intro x y rxy
      simp
      apply sound
      apply h
      assumption
  }

@[simp] def mapRingHom_mk (f: α →+* β) {h} : mapRingHom f h (mk r x) = mk s (f x) := rfl

end AlgQuot

section

instance : IsLeftDistrib ℕ where
  mul_add := Nat.mul_add
instance : IsRightDistrib ℕ := inferInstance
instance : IsSemiring ℕ where

instance : IsLeftDistrib ℤ where
  mul_add := Int.mul_add
instance : IsRightDistrib ℤ := inferInstance
instance : IsSemiring ℤ where

end

namespace OfEquiv

variable (f: α ≃ β)

protected scoped instance [SemiringOps β] : SemiringOps (OfEquiv f) := inferInstance

protected scoped instance [Add β] [Mul β] [IsLeftDistrib β] : IsLeftDistrib (OfEquiv f) where
  mul_add k a b := by dsimp; rw [Equiv.symm_coe]; rw [mul_add]; iterate 2 rw [Equiv.symm_coe]
protected scoped instance [Add β] [Mul β] [IsRightDistrib β] : IsRightDistrib (OfEquiv f) where
  add_mul k a b := by dsimp; rw [Equiv.symm_coe]; rw [add_mul]; iterate 2 rw [Equiv.symm_coe]

protected scoped instance [AddMonoidOps β] [Mul β] [IsNonUnitalNonAssocSemiring β] : IsNonUnitalNonAssocSemiring (OfEquiv f) where

protected scoped instance [AddMonoidOps β] [Mul β] [IsNonUnitalSemiring β] : IsNonUnitalSemiring (OfEquiv f) where

protected scoped instance [AddMonoidWithOneOps β] [Mul β] [IsNonAssocSemiring β] : IsNonAssocSemiring (OfEquiv f) where

protected scoped instance [SemiringOps β] [IsSemiring β] : IsSemiring (OfEquiv f) where

def ringEquiv [Zero β] [One β] [Add β] [Mul β] : OfEquiv f ≃+* β where
  toEquiv := f
  map_zero := by dsimp; rw [Equiv.symm_coe]
  map_one := by dsimp; rw [Equiv.symm_coe]
  map_add _ _ := by dsimp; rw [Equiv.symm_coe]
  map_mul _ _ := by dsimp; rw [Equiv.symm_coe]

end OfEquiv
