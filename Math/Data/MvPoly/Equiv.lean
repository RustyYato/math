module

import Math.Data.MvPoly.Defs
import Math.Data.Poly.Defs

namespace Math


variable [SemiringOps R] [IsSemiring R] [IsComm R]

example : MvPoly Unit R ≃ₐ[R] Poly R where
  toAlgebraHom := MvPoly.eval (fun _ => Poly.X)
  invFun := Poly.eval (MvPoly.X (α := R) ())
  leftInv p := by
    show MvPoly.eval _ _ = _
    induction p with
    | C => rw [←Poly.algebraMap_eq_C, map_algebraMap, map_algebraMap]
    | add => rw [map_add, map_add]; congr
    | mul => rw [map_mul, map_mul]; congr
    | X => rw [Poly.eval_X, MvPoly.eval_X]
  rightInv p := by
    show Poly.eval _ (MvPoly.eval _ _) = _
    induction p with
    | algebraMap  => rw [map_algebraMap, map_algebraMap]
    | add => rw [map_add, map_add]; congr
    | mul => rw [map_mul, map_mul]; congr
    | X => rw [MvPoly.eval_X, Poly.eval_X]
