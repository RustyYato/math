module

public import Math.Algebra.Module.Set.Defs
public import Math.Algebra.LinearCombo.Defs

namespace Math

namespace IsModule

variable {α: Type*} (R: Type*)
  [SemiringOps R] [IsSemiring R] [SMul R α]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] [IsModule R α]

public def eval (U: Set α) : LinearCombo U R →ₗ[R] α :=
  LinearCombo.lift (fun x: U => x.val)

public theorem eval_ι (U: Set α) (u: U) : eval R U (.ι R u a) = a • u.val :=
  LinearCombo.lift_ι _ _ _

public abbrev IsLinearIndependent (U: Set α) :=
  Function.Injective (eval R U)

public structure IsBasis (U: Set α) where
  linindep: IsLinearIndependent R U
  complete: ∀x: α, x ∈ Submodule.span R U

end IsModule

namespace LinearCombo

variable (R: Type*) [SemiringOps R] [IsSemiring R]

public def cast {U V: Set α} (h: U ⊆ V) : LinearCombo U R →ₗ[R] LinearCombo V R :=
  LinearCombo.lift (fun x: U => .ι R (⟨x.val, h _ x.property⟩: V) 1)

public theorem cast_ι {U V: Set α} (h: U ⊆ V) (x: U) (r: R) : cast R h (.ι R x r) = .ι R ⟨x.val, h _ x.property⟩ r := by
  unfold cast; rw [LinearCombo.lift_ι, ←map_smul, smul_eq_mul, mul_one]

public def filter {U: Set α} (V: Set α) [DecidablePred (· ∈ V)] : LinearCombo U R →ₗ[R] LinearCombo V R :=
  LinearCombo.lift <| fun x: U =>
    if h:x.val ∈ V then
      .ι R (⟨x.val, h⟩: V) 1
    else
      0

public theorem filter_ι_mem {U V: Set α} [DecidablePred (· ∈ V)] (x: U) (h: x.val ∈ V) (r: R) : filter R V (.ι R x r) = .ι R ⟨x.val, h⟩ r := by
  unfold filter; rw [LinearCombo.lift_ι, dite_eq_left h, ←map_smul, smul_eq_mul, mul_one]

public theorem filter_ι_not_mem {U V: Set α} [DecidablePred (· ∈ V)] (x: U) (h: x.val ∉ V) (r: R) : filter R V (.ι R x r) = 0 := by
  unfold filter; rw [LinearCombo.lift_ι, dite_eq_right h, smul_zero]

public theorem filter_get_mem {U V: Set α} [DecidableEq U] [DecidableEq V] [DecidablePred (· ∈ V)] (x: U) (h: x.val ∈ V) (lc: LinearCombo U R) :
  (filter R V lc).get ⟨x.val, h⟩ = LinearCombo.get x lc := by
  induction lc with
  | zero => simp [map_zero]
  | add a b iha ihb => simp [map_add, iha, ihb]
  | ι i a =>
  by_cases hv:i.val ∈ V
  rw [filter_ι_mem]
  by_cases h:i.val = x.val
  obtain ⟨i, hi⟩ := i; obtain ⟨x, hx⟩ := x
  cases h; dsimp; rw [LinearCombo.get_ι_eq, LinearCombo.get_ι_eq]
  rw [LinearCombo.get_ι_ne, LinearCombo.get_ι_ne]
  intro rfl; contradiction
  obtain ⟨i, hi⟩ := i; obtain ⟨x, hx⟩ := x
  intro g; cases g; contradiction
  assumption
  rw [LinearCombo.filter_ι_not_mem, map_zero, LinearCombo.get_ι_ne]
  intro rfl; contradiction
  assumption

end LinearCombo
