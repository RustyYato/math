module

public import Math.Algebra.AddMonoidWithOne.Defs
public import Math.Algebra.MonoidWithZero.Defs

namespace Math

section Property

public class IsLeftDistrib (α: Type*) [Add α] [Mul α] where
  mul_add (k a b: α) : k * (a + b) = k * a + k * b

public class IsRightDistrib (α: Type*) [Add α] [Mul α] where
  add_mul (a b k: α) : (a + b) * k = a * k + b * k

export IsLeftDistrib (mul_add)
export IsRightDistrib (add_mul)

public class SemiringOps (α: Type*)
  extends AddMonoidOps α, MonoidOps α, NatCast α where

public instance [AddMonoidOps α] [MonoidOps α] [NatCast α] : SemiringOps α where

public class IsNonUnitalNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] extends IsAddMonoid α, IsLeftDistrib α, IsRightDistrib α, IsLawfulZeroMul α, IsAddComm α  where

public class IsNonUnitalSemiring (α: Type*)
  [AddMonoidOps α] [Mul α] extends IsNonUnitalNonAssocSemiring α, IsSemigroup α where

public class IsNonAssocSemiring (α: Type*)
  [AddMonoidOps α] [One α] [Mul α] [NatCast α] extends IsNonUnitalNonAssocSemiring α, IsAddMonoidWithOne α, IsLawfulOne α where

public class IsSemiring (α: Type*) [SemiringOps α] : Prop extends IsNonUnitalSemiring α, IsNonAssocSemiring α, IsMonoidWithZero α where

end Property

section Hom

section Defs

public structure RingHom (α β: Type*)
  [Add α] [Mul α] [Zero α] [One α]
  [Add β] [Mul β] [Zero β] [One β] extends α →+ β, α →* β where

public structure RingEmbedding (α β: Type*)
  [Add α] [Mul α] [Zero α] [One α]
  [Add β] [Mul β] [Zero β] [One β] extends α ↪ β, RingHom α β where

public structure RingEquiv (α β: Type*)
  [Add α] [Mul α] [Zero α] [One α]
  [Add β] [Mul β] [Zero β] [One β] extends α ≃ β, RingHom α β,
    α ≃+ β, α ≃* β where

infixr:80 " →+* " => RingHom
infixr:80 " ↪+* " => RingEmbedding
infixr:80 " ≃+* " => RingEquiv

end Defs

section Impls

variable [Add α] [Add β] [Mul α] [Mul β] [Zero α] [Zero β] [One α] [One β]

public instance : Funlike (α →+* β) α β where
public instance : EmbeddingLike (α ↪+* β) α β where
public instance : EquivLike (α ≃+* β) α β where

public instance : IsZeroHom (α →+* β) α β where
public instance : IsZeroHom (α ↪+* β) α β where
public instance : IsZeroHom (α ≃+* β) α β where

public instance : IsOneHom (α →+* β) α β where
public instance : IsOneHom (α ↪+* β) α β where
public instance : IsOneHom (α ≃+* β) α β where

public instance : IsAddHom (α →+* β) α β where
public instance : IsAddHom (α ↪+* β) α β where
public instance : IsAddHom (α ≃+* β) α β where

public instance : IsMulHom (α →+* β) α β where
public instance : IsMulHom (α ↪+* β) α β where
public instance : IsMulHom (α ≃+* β) α β where

end Impls

variable {α β γ: Type*} [Add α] [Mul α] [Zero α] [One α] [Add β] [Mul β] [Zero β] [One β] [Add γ] [Mul γ] [Zero γ] [One γ]

section Reduction

@[simp] public theorem RingEmbedding.apply_toEmbedding (f: α ↪+* β) (x: α) : f.toEmbedding x = f x := rfl
@[simp] public theorem RingEquiv.apply_toEquiv (f: α ≃+* β) (x: α) : f.toEquiv x = f x := rfl
@[simp] public theorem RingEmbedding.apply_toRingHom (f: α ↪+* β) (x: α) : f.toRingHom x = f x := rfl
@[simp] public theorem RingEquiv.apply_toRingHom (f: α ≃+* β) (x: α) : f.toRingHom x = f x := rfl

@[ext] public theorem RingHom.ext (f g: α →+* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem RingEmbedding.ext (f g: α ↪+* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h
@[ext] public theorem RingEquiv.ext (f g: α ≃+* β) (h: ∀i, f i = g i) : f = g := DFunlike.ext _ _ h

end Reduction

section Api

@[expose] public protected def RingHom.id (α: Type*) [Add α] [Mul α] [Zero α] [One α] : α →+* α := {
  AddGroupHom.id α, GroupHom.id α with
}
@[expose] public protected def RingEmbedding.id (α: Type*) [Add α] [Mul α] [Zero α] [One α] : α ↪+* α := {
  Embedding.id _, RingHom.id _ with
}
@[expose] public protected def RingEquiv.id (α: Type*) [Add α] [Mul α] [Zero α] [One α] : α ≃+* α := {
  Equiv.id _, RingHom.id _ with
}

@[expose] public def RingHom.comp (f: β →+* γ) (g: α →+* β) : α →+* γ := {
  f.toAddGroupHom.comp g.toAddGroupHom, f.toGroupHom.comp g.toGroupHom with
}
@[expose] public def RingEmbedding.comp (f: β ↪+* γ) (g: α ↪+* β) : α ↪+* γ := {
  f.toEmbedding.comp g.toEmbedding, f.toRingHom.comp g.toRingHom with
}
@[expose] public def RingEquiv.comp (f: β ≃+* γ) (g: α ≃+* β) : α ≃+* γ := {
  f.toEquiv.comp g.toEquiv, f.toRingHom.comp g.toRingHom with
}
@[expose] public def RingEmbedding.trans (f: α ↪+* β) (g: β ↪+* γ) : α ↪+* γ := comp g f
@[expose] public def RingEquiv.trans (f: α ≃+* β) (g: β ≃+* γ) : α ≃+* γ := comp g f
@[expose] public def RingEquiv.symm (f: α ≃+* β) : β ≃+* α := {
  f.toAddGroupEquiv.symm, f.toGroupEquiv.symm with
}

end Api

namespace RingHom

@[simp] public theorem apply_id : RingHom.id α x = x := rfl

@[simp] public theorem apply_comp (f: β →+* γ) (g: α →+* β) (x: α) : f.comp g x = f (g x) := rfl

end RingHom

namespace RingEmbedding

@[simp] public theorem apply_id : RingEmbedding.id α x = x := rfl

@[simp] public theorem apply_comp (f: β ↪+* γ) (g: α ↪+* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ↪+* β) (g: β ↪+* γ) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: α ↪+* β) : Function.Injective f := f.injective

end RingEmbedding

namespace RingEquiv

@[simp] public theorem apply_id : RingEquiv.id α x = x := rfl

@[simp] public theorem apply_symm (f: α ≃+* β) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: α ≃+* β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: α ≃+* β) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: β ≃+* γ) (g: α ≃+* β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: α ≃+* β) (g: β ≃+* γ) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: α ≃+* β) : f.symm.comp f = RingEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: α ≃+* β) : f.comp f.symm = RingEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: α ≃+* β) : f.symm.trans f = RingEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: α ≃+* β) : f.trans f.symm = RingEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: α ≃+* β) : Function.Injective f := f.rightInv.injective
public theorem surj (f: α ≃+* β) : Function.Surjective f := f.symm.rightInv.surjective

@[expose] public def ofParts
  [IsLawfulOne α] [IsLawfulOne β]
  [IsLawfulZero α] [IsLawfulZero β]
  (f: α ≃ β)
  (map_add: ∀a b , f (a + b) = f a + f b)
  (map_mul: ∀a b , f (a * b) = f a * f b)
  : α ≃+* β where
  toEquiv := f
  map_add := map_add
  map_mul := map_mul
  map_zero :=
    let f' : α ≃+ₙ β := {
      toEquiv := f
      map_add := map_add
    }
    map_zero (AddGroupHom.of_add f')
  map_one :=
    let f' : α ≃*ₙ β := {
      toEquiv := f
      map_mul := map_mul
    }
    map_one (GroupHom.of_mul f')

@[simp] public theorem apply_ofParts
  [IsLawfulOne α] [IsLawfulOne β]
  [IsLawfulZero α] [IsLawfulZero β]
  (f: α ≃ β)
  (map_add: ∀a b , f (a + b) = f a + f b)
  (map_mul: ∀a b , f (a * b) = f a * f b)
  (x: α) : ofParts f map_add map_mul x = f x := rfl

end RingEquiv

end Hom

section Basics

public instance : IsSemiring ℕ where
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
public instance : IsSemiring ℤ where
  mul_add := Int.mul_add
  add_mul := Int.add_mul

end Basics

section Theorems

variable [SemiringOps α] [IsSemiring α]

public theorem nsmul_eq_natCast_mul (n: ℕ) (a: α) : n • a = n * a := by
  induction n with
  | zero => rw [natCast_zero, zero_mul, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, add_mul, one_mul, ih]

public theorem nsmul_eq_mul_natCast (n: ℕ) (a: α) : n • a = a * n := by
  induction n with
  | zero => rw [natCast_zero, mul_zero, zero_nsmul]
  | succ n ih => rw [natCast_succ, succ_nsmul, mul_add, mul_one, ih]

public theorem natCast_mul (n m: ℕ) : (n * m: ℕ) = (n: α) * m := by
  rw [←nsmul_one_eq_natCast, mul_nsmul, nsmul_one_eq_natCast, nsmul_eq_natCast_mul]

@[expose] public def RingHom.natCast : ℕ →+* α where
  toFun := Nat.cast
  map_zero := natCast_zero
  map_one := natCast_one
  map_add := natCast_add
  map_mul := natCast_mul

@[simp] public theorem RingHom.apply_natCast (n: ℕ) : RingHom.natCast n = (n: α) := rfl

public instance : Subsingleton (ℕ →+* α) where
  allEq := by
    suffices ∀f: ℕ →+* α, f = RingHom.natCast by
      intro a b; rw [this a, this b]
    intro f; ext z
    show f (Nat.cast z) = _
    rw [RingHom.apply_natCast, map_natCast]

public theorem natCast_pown (n m: ℕ) : (n ^ m: ℕ) = (n: α) ^ m :=
  map_pown (f := RingHom.natCast) _ _

public theorem two_mul (a: α) : (2: ℕ) * a = a + a := by
  rw [←nsmul_eq_natCast_mul, succ_nsmul, one_nsmul]

public theorem add_sq (a b: α) [IsCommAt a b] : (a + b) ^ 2 = a ^ 2 + (2: ℕ) * (a * b) + b ^ 2 := by
  rw [pown_succ, pown_one, mul_add, add_mul, add_mul, mul_comm b,
    ←add_assoc, add_assoc (a * a), ←two_mul, ←pown_two, ←pown_two]

public instance (n: ℕ) (a: α) : IsCommAt (n: α) a where
  mul_comm := by rw [←nsmul_eq_mul_natCast, ←nsmul_eq_natCast_mul]

end Theorems

namespace OfEquiv

variable (f: α ≃ β)

public instance [Mul α] [Add α] [IsLeftDistrib α] : IsLeftDistrib (OfEquiv f) where
  mul_add a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    simp; rw [mul_add]
public instance [Mul α] [Add α] [IsRightDistrib α] : IsRightDistrib (OfEquiv f) where
  add_mul a b c := by
    induction a with | _ a =>
    induction b with | _ b =>
    induction c with | _ c =>
    simp; rw [add_mul]

public instance [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α] : IsNonUnitalNonAssocSemiring (OfEquiv f) where
public instance [AddMonoidOps α] [Mul α] [IsNonUnitalSemiring α] : IsNonUnitalSemiring (OfEquiv f) where
public instance [AddMonoidOps α] [One α] [Mul α] [NatCast α] [IsNonAssocSemiring α] : IsNonAssocSemiring (OfEquiv f) where
public instance [SemiringOps α] [IsSemiring α] : IsSemiring (OfEquiv f) where

end OfEquiv
