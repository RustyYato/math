module

public import Math.Algebra.Monoid.Defs.Hom
import Math.Algebra.Monoid.Defs.Lemmas

namespace Math

namespace GroupHom

@[expose] public def of_mul
  [One α] [Mul α] [IsLawfulOne α]
  [One β] [Mul β] [IsLawfulOne β]
  [SurjectionLike F α β] [IsMulHom F α β] (f: F) : α →* β where
  toFun := f
  map_mul := map_mul f
  map_one := by
    have ⟨a, ha⟩ := SurjectionLike.coeSurjection f 1
    rw (occs := [1]) [←mul_one (f 1), ←ha, ←map_mul f]
    rw [one_mul, ha]

@[simp] public theorem apply_of_mul
  [One α] [Mul α] [IsLawfulOne α]
  [One β] [Mul β] [IsLawfulOne β]
  [SurjectionLike F α β] [IsMulHom F α β] (f: F) (a: α) : of_mul f a = f a := rfl

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

@[expose] public def of_add
  [Zero α] [Add α] [IsLawfulZero α]
  [Zero β] [Add β] [IsLawfulZero β]
  [SurjectionLike F α β] [IsAddHom F α β] (f: F) : α →+ β where
  toFun := f
  map_add := map_add f
  map_zero := by
    have ⟨a, ha⟩ := SurjectionLike.coeSurjection f 0
    rw (occs := [1]) [←add_zero (f 0), ←ha, ←map_add f]
    rw [zero_add, ha]

@[simp] public theorem apply_of_add
  [Zero α] [Add α] [IsLawfulZero α]
  [Zero β] [Add β] [IsLawfulZero β]
  [SurjectionLike F α β] [IsAddHom F α β] (f: F) (a: α) : of_add f a = f a := rfl

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

namespace GroupEquiv

@[expose] public def of_mul
  [One α] [Mul α] [IsLawfulOne α]
  [One β] [Mul β] [IsLawfulOne β]
  [EquivLike F α β] [IsMulHom F α β] (f: F) : α ≃* β := {
  Equiv.coe f, GroupHom.of_mul f with
}

@[simp] public theorem apply_of_mul
  [One α] [Mul α] [IsLawfulOne α]
  [One β] [Mul β] [IsLawfulOne β]
  [EquivLike F α β] [IsMulHom F α β] (f: F) (a: α) : of_mul f a = f a := rfl

end GroupEquiv

namespace AddGroupEquiv

@[expose] public def of_add
  [Zero α] [Add α] [IsLawfulZero α]
  [Zero β] [Add β] [IsLawfulZero β]
  [EquivLike F α β] [IsAddHom F α β] (f: F) : α ≃+ β := {
  Equiv.coe f, AddGroupHom.of_add f with
}

@[simp] public theorem apply_of_add
  [Zero α] [Add α] [IsLawfulZero α]
  [Zero β] [Add β] [IsLawfulZero β]
  [EquivLike F α β] [IsAddHom F α β] (f: F) (a: α) : of_add f a = f a := rfl

end AddGroupEquiv
