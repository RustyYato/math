module

public import Math.Algebra.Module.Defs

namespace Math

public class AlgebraMap (R α: Type*) [SemiringOps R] [SemiringOps α] extends R →+* α where

@[expose] public def algebraMap (R: Type*) {α: Type*} [SemiringOps R] [SemiringOps α] [AlgebraMap R α] : R →+* α :=
  AlgebraMap.toRingHom

public class IsAlgebra (R α: Type*) [SemiringOps R] [SemiringOps α] [IsSemiring R] [IsSemiring α] [AlgebraMap R α] [SMul R α] where
  commutes (r: R) (a: α) : algebraMap R r * a = a * algebraMap R r
  smul_def (r: R) (a: α) : r • a = algebraMap R r * a

export IsAlgebra (commutes smul_def)

variable [SemiringOps R] [SemiringOps α] [AlgebraMap R α] [SMul R α]

public instance [IsSemiring R] [IsSemiring α] [IsAlgebra R α] (r: R) (a: α) : IsCommAt (algebraMap R r) a where
  mul_comm := by rw [commutes]
public instance [IsSemiring R] [IsSemiring α] [IsAlgebra R α] (r: R) (a: α) : IsCommAt a (algebraMap R r) := inferInstance

public instance (priority := 900) : AlgebraMap R R where
  toRingHom := {
    toFun := id
    map_one := rfl
    map_zero := rfl
    map_add _ _ := rfl
    map_mul _ _ := rfl
  }

@[simp] public theorem apply_algebraMap_id (r: R) : algebraMap R r = r := rfl

public instance [IsSemiring α] [IsComm α] : IsAlgebra α α where
  commutes _ _ := mul_comm _ _
  smul_def _ _ := rfl

public instance [IsSemiring R] : AlgebraMap ℕ R where
  toRingHom := RingHom.natCast

public instance [IsSemiring R] : IsAlgebra ℕ R where
  commutes r x := by
    show r * x = x * r
    rw [←nsmul_eq_natCast_mul, ←nsmul_eq_mul_natCast]
  smul_def a b := by rw [nsmul_eq_natCast_mul]; rfl

public instance [IsSemiring R] [IsSemiring α] [IsAlgebra R α] : IsModule R α where
  one_smul a := by rw [smul_def, map_one, one_mul]
  mul_smul r s a := by rw [smul_def, smul_def, smul_def, map_mul, mul_assoc]
  smul_zero r := by rw [smul_def, mul_zero]
  smul_add r a b := by rw [smul_def, smul_def, smul_def, mul_add]
  zero_smul a := by rw [smul_def, map_zero, zero_mul]
  add_smul r s a := by rw [smul_def, smul_def, smul_def, map_add, add_mul]
