module

public import Math.Algebra.Module.Defs
public import Math.Algebra.Module.Hom.Defs

namespace Math

public inductive FreeModule.Pre (R α: Type*) where
| zero
| of (a: α)
| smul (r: R) (a: Pre R α)
| add (a b: Pre R α)

public instance : Zero (FreeModule.Pre R α) where
  zero := .zero
public instance : Add (FreeModule.Pre R α) where
  add := .add
public instance : SMul R (FreeModule.Pre R α) where
  smul := .smul

public inductive FreeModule.Rel {R α: Type*} [Zero R] [One R] [Add R] [Mul R] : FreeModule.Pre R α -> FreeModule.Pre R α -> Prop where
| refl (a: Pre R α) : Rel a a
| symm {a b: Pre R α} : Rel a b -> Rel b a
| trans {a b c: Pre R α} : Rel a b -> Rel b c -> Rel a c

| add_assoc (a b c: Pre R α) : Rel (a + b + c) (a + (b + c))
| add_zero (a: Pre R α) : Rel (a + 0) a
| zero_add (a: Pre R α) : Rel (0 + a) a

| one_smul (a: Pre R α) : Rel ((1: R) • a) a
| mul_smul (r s: R) (a: Pre R α) : Rel ((r * s) • a) (r • s • a)
| zero_smul (a: Pre R α) : Rel ((0: R) • a) 0
| add_smul (r s: R) (a: Pre R α) : Rel ((r + s) • a) (r • a + s • a)
| smul_zero (r: R) : Rel (r • (0: Pre R α)) 0
| smul_add (r: R) (a b: Pre R α) : Rel (r • (a + b)) (r • a + r • b)

| smul_congr (r: R) (a b: Pre R α) : Rel a b -> Rel (r • a) (r • b)
| add_congr (a b c d: Pre R α) : Rel a c -> Rel b d -> Rel (a + b) (c + d)

public instance FreeModule.Pre.setoid (R α: Type*) [Zero R] [One R] [Add R] [Mul R] : Setoid (FreeModule.Pre R α) where
  r := FreeModule.Rel
  iseqv := ⟨.refl, .symm, .trans⟩

public structure FreeModule (R α: Type*) [Zero R] [One R] [Add R] [Mul R] where
  ofQuot :: toQuot : Quotient (FreeModule.Pre.setoid R α)

namespace FreeModule

section

public def mk (R: Type*) [Zero R] [One R] [Add R] [Mul R] (val: Pre R α) : FreeModule R α where
  toQuot := Quotient.mk _ val

public def ι (R: Type*) [Zero R] [One R] [Add R] [Mul R] : α -> FreeModule R α := mk R ∘ .of

variable {R: Type*} [Zero R] [One R] [Add R] [Mul R]

public def lift' (f: Pre R α -> γ) (hf: ∀a b, a ≈ b -> f a = f b) (val: FreeModule R α) : γ :=
  val.toQuot.lift f hf

public def lift₂' (f: Pre R α -> Pre R α -> γ) (hf: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a b: FreeModule R α) : γ :=
  a.toQuot.liftOn₂ b.toQuot f hf

theorem sound : a ≈ b -> mk R a = mk R b := by
  intro h; unfold mk; congr 1
  apply Quotient.sound
  assumption

theorem ind {motive: FreeModule R α -> Prop} (mk: ∀a, motive (mk R a)) (a: FreeModule R α) : motive a := by
  obtain ⟨a⟩ := a
  induction a using Quotient.ind
  apply mk

end

variable [SemiringOps R] [IsSemiring R]

public instance  : Zero (FreeModule R α) where
  zero := mk R 0

public instance  : SMul R (FreeModule R α) where
  smul r := lift' (fun a => mk R (r • a)) <| by
    intro a b h; apply sound
    apply Rel.smul_congr
    assumption

public instance  : Add (FreeModule R α) where
  add := lift₂' (fun a b => mk R (a + b)) <| by
    intro a b c d h g; apply sound
    apply Rel.add_congr
    assumption
    assumption

public instance  : IsLawfulZero (FreeModule R α) where
  add_zero a := by
    induction a using ind
    apply sound
    apply Rel.add_zero
  zero_add a := by
    induction a using ind
    apply sound
    apply Rel.zero_add

public instance  : IsAddSemigroup (FreeModule R α) where
  add_assoc a b c := by
    induction a using ind
    induction b using ind
    induction c using ind
    apply sound
    apply Rel.add_assoc

public instance : IsLawfulOneSMul R (FreeModule R α) where
  one_smul a := by
    induction a using ind
    apply sound; apply Rel.one_smul
public instance : IsLawfulZeroSMul R (FreeModule R α) where
  zero_smul a := by
    induction a using ind
    apply sound; apply Rel.zero_smul
public instance : IsLeftDistribSMul R (FreeModule R α) where
  add_smul r s a := by
    induction a using ind
    apply sound; apply Rel.add_smul

public instance  : SMul ℕ (FreeModule R α) where
  smul n a := (n: R) • a
public instance  : IsLawfulNSMul (FreeModule R α) where
  zero_nsmul a := by
    induction a using ind with | _ a =>
    show mk R _ = mk R _
    rw [natCast_zero]
    show (0: R) • mk R a = 0
    rw [zero_smul]
  succ_nsmul a n := by
    induction a using ind with | _ a =>
    show mk R _ = mk R _
    rw [natCast_succ]
    show (n + 1: R) • mk R _ = mk R _
    rw [add_smul, one_smul]; rfl

public instance  : IsAddMonoid (FreeModule R α) where

public instance : IsModule R (FreeModule R α) where
  smul_add r a b := by
    induction a using ind
    induction b using ind
    apply sound; apply Rel.smul_add
  mul_smul r s a := by
    induction a using ind
    apply sound; apply Rel.mul_smul
  zero_smul a := by
    induction a using ind
    apply sound; apply Rel.zero_smul
  smul_zero r := by
    apply sound; apply Rel.smul_zero

@[induction_eliminator]
public theorem induction
  {R α: Type*} [SemiringOps R] [IsSemiring R]
  {motive: FreeModule R α -> Prop}
  (zero: motive 0)
  (ι: ∀a, motive (ι R a))
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (smul: ∀(r: R) a, motive a -> motive (r • a))
  (m: FreeModule R α) : motive m := by
  induction m using ind with | _ m =>
  induction m with
  | zero => apply zero
  | of => apply ι
  | add a b => apply add (mk R a) (mk R b) <;> assumption
  | smul r a => apply smul r (mk R a) <;> assumption

variable [AddMonoidOps M] [IsAddMonoid M] [SMul R M] [IsModule R M]

def preLift (f: α -> M) : Pre R α -> M
| .zero => 0
| .of a => f a
| .smul r a => r • preLift f a
| .add a b => preLift f a + preLift f b

def preLift' (f: α -> M) : FreeModule R α →ₗ[R] M where
  toFun := lift' (preLift f) <| by
    intro a b h; induction h with
    | refl => rfl
    | symm => symm; assumption
    | trans => apply Eq.trans <;> assumption
    | add_assoc => apply add_assoc
    | add_zero => apply add_zero
    | zero_add => apply zero_add
    | one_smul => apply one_smul
    | mul_smul => apply mul_smul
    | zero_smul => apply zero_smul
    | add_smul => apply add_smul
    | smul_zero => apply smul_zero
    | smul_add => apply smul_add
    | smul_congr r => show _ • _ = _ • _; congr
    | add_congr  => show _ + _ = _ + _; congr
  map_add a b := by
    induction a using ind
    induction b using ind
    rfl
  map_smul r a := by
    induction a using ind
    rfl

public def lift : (α -> M) ≃ (FreeModule R α →ₗ[R] M) where
  toFun := preLift'
  invFun f := f ∘ ι R
  leftInv := by
    intro f; ext a
    induction a with
    | zero => rw [map_zero, map_zero]
    | ι => rfl
    | add => rw [map_add, map_add]; congr
    | smul => rw [map_smul, map_smul]; congr
  rightInv := by intro f; ext a; rfl

@[simp] public theorem lift_ι (f: α -> M) (a: α) : lift f (ι R a) = f a := by rfl

end FreeModule
