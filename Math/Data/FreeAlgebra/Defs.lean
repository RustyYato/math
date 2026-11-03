module

public import Math.Algebra.Algebra.Defs
import Math.Algebra.RingQuot.Defs
import Math.Logic.UniqueChoice

namespace Math

section Pre

public inductive FreeAlgebra.Pre (R α: Type*) [SemiringOps R] [IsSemiring R] where
| of (a: α)
| scalar (r: R)
| add (a b: Pre R α)
| mul (a b: Pre R α)

variable {R α: Type*} [SemiringOps R] [IsSemiring R]

public instance : Zero (FreeAlgebra.Pre R α) where
  zero := .scalar 0
public instance : One (FreeAlgebra.Pre R α) where
  one := .scalar 1
public instance : Add (FreeAlgebra.Pre R α) where
  add := .add
public instance : Mul (FreeAlgebra.Pre R α) where
  mul := .mul

public inductive FreeAlgebra.Rel : Pre R α -> Pre R α -> Prop where
| refl (a: Pre R α) : Rel a a
| symm {a b: Pre R α} : Rel a b -> Rel b a
| trans {a b c: Pre R α} : Rel a b -> Rel b c -> Rel a c

| scalar_add (a b: R) : Rel (Pre.scalar a + Pre.scalar b) (Pre.scalar (a + b))
| scalar_mul (a b: R) : Rel (Pre.scalar a * Pre.scalar b) (Pre.scalar (a * b))
| central_scalar (r: R) (a: Pre R α) : Rel (Pre.scalar r * a) (a * Pre.scalar r)

| add_zero (a: Pre R α) : Rel (a + 0) a
| zero_add (a: Pre R α) : Rel (0 + a) a
| add_comm (a b: Pre R α) : Rel (a + b) (b + a)

| mul_zero (a: Pre R α) : Rel (a * 0) 0
| zero_mul (a: Pre R α) : Rel (0 * a) 0

| mul_one (a: Pre R α) : Rel (a * 1) a
| one_mul (a: Pre R α) : Rel (1 * a) a

| add_assoc (a b c: Pre R α) : Rel (a + b + c) (a + (b + c))
| mul_assoc (a b c: Pre R α) : Rel (a * b * c) (a * (b * c))

| mul_add (k a b: Pre R α) : Rel (k * (a + b)) (k * a + k * b)
| add_mul (k a b: Pre R α) : Rel ((a + b) * k) (a * k + b * k)

| add_congr (a b c d: Pre R α) : Rel a c -> Rel b d -> Rel (a + b) (c + d)
| mul_congr (a b c d: Pre R α) : Rel a c -> Rel b d -> Rel (a * b) (c * d)

public instance FreeAlgebra.Pre.setoid (R α: Type*) [SemiringOps R] [IsSemiring R] : Setoid (FreeAlgebra.Pre R α) where
  r := FreeAlgebra.Rel
  iseqv := ⟨FreeAlgebra.Rel.refl, FreeAlgebra.Rel.symm, FreeAlgebra.Rel.trans⟩

end Pre

public structure FreeAlgebra (R α: Type*) [SemiringOps R] [IsSemiring R] where
  ofQuot :: toQuot : Quotient (FreeAlgebra.Pre.setoid R α)

namespace FreeAlgebra

variable [SemiringOps R] [IsSemiring R]

public abbrev mk (r: Pre R α) : FreeAlgebra R α where
  toQuot := Quotient.mk _ r
abbrev sound' (a b: Pre R α) (h: a ≈ b) : mk a = mk b := by
  unfold mk; congr 1; apply Quotient.sound
  assumption
public abbrev lift' (f: Pre R α -> γ) (hf: ∀a b, a ≈ b -> f a = f b) (a: FreeAlgebra R α) : γ :=
  a.toQuot.lift f hf
public abbrev lift₂' (f: Pre R α -> Pre R α -> γ) (hf: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: FreeAlgebra R α) : γ :=
  a.toQuot.liftOn₂ b.toQuot f hf
abbrev ind {motive: FreeAlgebra R α -> Prop} (mk: ∀p, motive (mk p)) (r: FreeAlgebra R α) : motive r := by
  obtain ⟨r⟩ := r
  induction r using Quotient.ind
  apply mk

public instance : NatCast (FreeAlgebra R α) where
  natCast n := mk (.scalar n)
public instance : Zero (FreeAlgebra R α) where
  zero := mk (.scalar 0)
public instance : One (FreeAlgebra R α) where
  one := mk (.scalar 1)
public instance : Add (FreeAlgebra R α) where
  add := lift₂' (fun a b => mk (a + b)) <| by
    intro a b c d h g
    apply sound'
    apply Rel.add_congr <;> assumption
public instance : Mul (FreeAlgebra R α) where
  mul := lift₂' (fun a b => mk (a * b)) <| by
    intro a b c d h g
    apply sound'
    apply Rel.mul_congr <;> assumption
public instance : SMul R (FreeAlgebra R α) where
  smul r a := mk (.scalar r) * a
public instance : SMul ℕ (FreeAlgebra R α) where
  smul r a := (r: R) • a

public instance : IsSemigroup (FreeAlgebra R α) where
  mul_assoc a b c := by
    induction a using ind with | _ a =>
    induction b using ind with | _ b =>
    induction c using ind with | _ c =>
    apply sound'; apply Rel.mul_assoc
public instance : IsLawfulOne (FreeAlgebra R α) where
  mul_one a := by
    induction a using ind with | _ a =>
    apply sound'; apply Rel.mul_one
  one_mul a := by
    induction a using ind with | _ a =>
    apply sound'; apply Rel.one_mul

public theorem scalar_add (a b: R) : mk (α := α) (.scalar (a + b)) = mk (.scalar a) + mk (.scalar b) := by
  symm; apply sound'; apply Rel.scalar_add
public theorem scalar_mul (a b: R) : mk (α := α) (.scalar (a * b)) = mk (.scalar a) * mk (.scalar b) := by
  symm; apply sound'; apply Rel.scalar_mul

open scoped DefaultPowN in
public instance : Pow (FreeAlgebra R α) ℕ := inferInstance
open scoped DefaultPowN in
public instance : IsLawfulPowN (FreeAlgebra R α) := inferInstance

public instance : IsMonoid (FreeAlgebra R α) where

public instance : IsLeftDistrib (FreeAlgebra R α) where
  mul_add a b c := by
    induction a using ind with | _ a =>
    induction b using ind with | _ b =>
    induction c using ind with | _ c =>
    apply sound'; apply Rel.mul_add

public instance : IsRightDistrib (FreeAlgebra R α) where
  add_mul a b c := by
    induction a using ind with | _ a =>
    induction b using ind with | _ b =>
    induction c using ind with | _ c =>
    apply sound'; apply Rel.add_mul

public instance : IsSemiring (FreeAlgebra R α) where
  add_assoc a b c := by
    induction a using ind with | _ a =>
    induction b using ind with | _ b =>
    induction c using ind with | _ c =>
    apply sound'; apply Rel.add_assoc
  add_zero a := by
    induction a using ind with | _ a =>
    apply sound'; apply Rel.add_zero
  zero_add a := by
    induction a using ind with | _ a =>
    apply sound'; apply Rel.zero_add
  zero_nsmul a := by
    induction a using ind with | _ a =>
    apply sound'; rw [natCast_zero]; apply Rel.zero_mul
  succ_nsmul a n := by
    show _ * _ = _
    rw [natCast_add, scalar_add, add_mul]
    congr; rw [natCast_one]; apply one_mul a
  mul_zero a := by
    induction a using ind with | _ a =>
    apply sound'; apply Rel.mul_zero
  zero_mul a := by
    induction a using ind with | _ a =>
    apply sound'; apply Rel.zero_mul
  add_comm a b := by
    induction a using ind with | _ a =>
    induction b using ind with | _ b =>
    apply sound'; apply Rel.add_comm
  natCast_zero := by
    show mk _ = mk _
    rw [natCast_zero]
  natCast_succ n := by
    show mk _ = mk _
    rw [natCast_succ, scalar_add]; rfl

public instance : AlgebraMap R (FreeAlgebra R α) where
  toFun := mk ∘ Pre.scalar
  map_zero := rfl
  map_one := rfl
  map_add := scalar_add
  map_mul := scalar_mul
public instance : IsAlgebra R (FreeAlgebra R α) where
  smul_def _ _ := rfl
  commutes r a := by
    induction a using ind with | _ a =>
    apply sound'; apply Rel.central_scalar

public def ι (R: Type*) [SemiringOps R] [IsSemiring R] : α -> FreeAlgebra R α := mk ∘ .of

@[induction_eliminator]
public theorem induction {motive: FreeAlgebra R α -> Prop}
  (algebraMap: ∀a, motive (algebraMap R a))
  (ι: ∀a, motive (ι R a))
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (a: FreeAlgebra R α) : motive a := by
  induction a using ind with | mk a =>
  induction a with
  | of a => apply ι
  | scalar => apply algebraMap
  | add a b => apply add (mk a) (mk b) <;> assumption
  | mul a b => apply mul (mk a) (mk b) <;> assumption

section Lift

variable
  (R: Type*)
  {α A}
  [SemiringOps R] [IsSemiring R]
  [SemiringOps A] [IsSemiring A] [AlgebraMap R A]
  [SMul R A] [IsAlgebra R A]

def preLift (f: α -> A) : FreeAlgebra.Pre R α -> A
| .of x => f x
| .scalar x => algebraMap R x
| .add a b => preLift f a + preLift f b
| .mul a b => preLift f a * preLift f b

def preLift' (f: α -> A) : FreeAlgebra R α →ₐ[R] A where
  toFun := lift' (preLift R f) <| by
    intro a b h
    induction h with
    | refl => rfl
    | symm => symm; assumption
    | trans => apply Eq.trans <;> assumption
    | scalar_add => symm; apply map_add (algebraMap R)
    | scalar_mul => symm; apply map_mul (algebraMap R)
    | central_scalar => apply commutes
    | add_zero =>
      dsimp [preLift]
      rw [map_zero]
      apply add_zero
    | zero_add =>
      dsimp [preLift]
      rw [map_zero]
      apply zero_add
    | add_comm => apply add_comm
    | mul_zero =>
      dsimp [preLift]
      rw [map_zero]
      apply mul_zero
    | zero_mul =>
      dsimp [preLift]
      rw [map_zero]
      apply zero_mul
    | mul_one =>
      dsimp [preLift]
      rw [map_one]
      apply mul_one
    | one_mul =>
      dsimp [preLift]
      rw [map_one]
      apply one_mul
    | add_assoc => apply add_assoc
    | mul_assoc => apply mul_assoc
    | mul_add => apply mul_add
    | add_mul => apply add_mul
    | add_congr => show _ + _ = _ + _; congr
    | mul_congr => show _ * _ = _ * _; congr
  map_zero := map_zero (algebraMap R)
  map_one := map_one (algebraMap R)
  map_add a b := by
    induction a using ind; induction b using ind
    rfl
  map_mul a b := by
    induction a using ind; induction b using ind
    rfl
  map_smul r a := by
    induction a using ind with | _ a =>
    rw [smul_def, smul_def]; rfl

public def lift : (α -> A) ≃ (FreeAlgebra R α →ₐ[R] A) where
  toFun f := preLift' R f
  invFun f x := f (ι R x)
  leftInv f := by
    dsimp; ext a
    induction a with
    | algebraMap => rw [map_algebraMap, map_algebraMap]
    | ι a => rfl
    | add => rw [map_add, map_add]; congr
    | mul => rw [map_mul, map_mul]; congr
  rightInv f := by
    dsimp; ext a
    rfl

#print lift

@[simp] public theorem lift_ι (f: α -> A) : lift R f (ι R a) = f a := by rfl

end Lift

variable {R: Type*} [SemiringOps R] [IsSemiring R] [IsZeroNeOne R] [IsComm R]

public theorem ι_inj [DecidableEq α] : Function.Injective (ι R (α := α)) := by
  intro a b h
  let f' (x: α) : R := if (x = b) then 1 else 0
  let f := lift R f'
  have : f (ι R b) = 1 := by
    dsimp [f]; rw [lift_ι]; unfold f'
    rw [ite_eq_left rfl]
  have : f (ι R a) = 1 := by
    rw [h, this]
  unfold f at this
  rw [lift_ι] at this
  unfold f' at this
  split at this
  assumption
  nomatch zero_ne_one this

public theorem ι_ne_algebraMap (a: α) (r: R) : ι R a ≠ algebraMap R r := by
  intro h

  let f₀ : FreeAlgebra R α →ₐ[R] R := lift R (fun _ => (0: R))
  let f₁ : FreeAlgebra R α →ₐ[R] R := lift R (fun _ => (1: R))

  have : f₀ (algebraMap R r) = f₁ (algebraMap R r) := by
    rw [map_algebraMap, map_algebraMap]
  rw [←h] at this
  dsimp [f₀, f₁] at this
  rw [lift_ι, lift_ι] at this
  exact zero_ne_one this

@[simp]
public theorem ι_ne_zero (a: α) : ι R a ≠ 0 :=
  ι_ne_algebraMap a (0: R)

@[simp]
public theorem ι_ne_one (a: α) : ι R a ≠ 1 :=
  ι_ne_algebraMap a (1: R)

end FreeAlgebra
