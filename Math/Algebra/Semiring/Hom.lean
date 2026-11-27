module

public import Math.Algebra.Semiring.Defs.Hom
public import Math.Algebra.Semiring.Defs.Lemmas
public import Math.Algebra.Monoid.Hom

namespace Math

variable [Zero α] [Zero β] [One α] [One β] [Add α] [Add β] [Mul α] [Mul β]

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
