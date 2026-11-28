module

public import Math.Algebra.Monoid.Defs.Hom
import Math.Algebra.Monoid.Defs.Lemmas

namespace Math

open scoped Automorphism

@[ext]
public structure SemidirectProduct (α β: Type*)
  [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β]
  (f: β →* α ≃* α) where
  fst: α
  snd: β

namespace SemidirectProduct

variable [MonoidOps α] [MonoidOps β] [IsMonoid α] [IsMonoid β]

public instance : One (SemidirectProduct α β f) where
  one := {
    fst := 1
    snd := 1
  }

public instance : Mul (SemidirectProduct α β f) where
  mul a b := {
    fst := a.fst * f a.snd b.fst
    snd := a.snd * b.snd
  }

@[simp] public theorem fst_one : (1: SemidirectProduct α β f).fst = 1 := rfl
@[simp] public theorem snd_one : (1: SemidirectProduct α β f).snd = 1 := rfl
@[simp] public theorem fst_mul (a b: SemidirectProduct α β f) : (a * b).fst = a.fst * f a.snd b.fst := rfl
@[simp] public theorem snd_mul (a b: SemidirectProduct α β f) : (a * b).snd = a.snd * b.snd := rfl

public instance : IsLawfulOne (SemidirectProduct α β f) where
  mul_one a := by
    ext <;> dsimp
    rw [map_one, mul_one]
    rw [mul_one]
  one_mul a := by
    ext <;> dsimp
    rw [map_one, one_mul]; rfl
    rw [one_mul]
public instance : IsSemigroup (SemidirectProduct α β f) where
  mul_assoc a b c := by
    ext <;> dsimp
    · rw [map_mul, map_mul, mul_assoc]; rfl
    · rw [mul_assoc]


public instance : Pow (SemidirectProduct α β f) ℕ :=
  DefaultPowN.instPowNat
public instance : IsLawfulPowN (SemidirectProduct α β f) :=
  DefaultPowN.instIsLawfulPowN

public instance : IsMonoid (SemidirectProduct α β f) where
