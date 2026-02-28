import LeanMath.Algebra.Algebra.Defs

namespace FreeAlgebra

private inductive Pre (R α: Type*) where
| scalar (r: R)
| of (a: α)
| add (a b: Pre R α)
| mul (a b: Pre R α)
-- this is an optimization, it doesn't actually give new powers
| nsmul (n: ℕ) (a: Pre R α)
| npow (a: Pre R α) (n: ℕ)

local instance : Coe R (Pre R α) where
  coe := .scalar
local instance : Coe α (Pre R α) where
  coe := .of

variable [SemiringOps R] [IsSemiring R]

local instance : Add (Pre R α) where
  add := .add
local instance : Mul (Pre R α) where
  mul := .mul
local instance : SMul ℕ (Pre R α) where
  smul := .nsmul
local instance : Pow (Pre R α) ℕ where
  pow := .npow
local instance : Zero (Pre R α) where
  zero := .scalar 0
local instance : One (Pre R α) where
  one := .scalar 1

private inductive Rel {R α: Type*} [SemiringOps R] : Pre R α -> Pre R α -> Prop where
| refl (a: Pre R α) : Rel a a
| symm {a b: Pre R α} : Rel a b -> Rel b a
| trans {a b c: Pre R α} : Rel a b -> Rel b c -> Rel a c

| scalar_add (a b: R) : Rel ((a + b: R)) (a + b: Pre R α)
| scalar_mul (a b: R) : Rel ((a * b: R)) (a * b: Pre R α)
| central (r: R) (a: Pre R α) : Rel ((r: Pre R α) * a) (a * r)

| zero_nsmul (a: Pre R α) : Rel (0 • a) 0
| succ_nsmul (n: ℕ) (a: Pre R α) : Rel ((n + 1) • a) (n • a + a)

| npow_zero (a: Pre R α) : Rel (a ^ 0) 1
| npow_succ (a: Pre R α) (n: ℕ) : Rel (a ^ (n + 1)) (a ^ n * a)

| add_zero (a: Pre R α) : Rel (a + 0) a
| zero_add (a: Pre R α) : Rel (0 + a) a

| mul_one (a: Pre R α) : Rel (a * 1) a
| one_mul (a: Pre R α) : Rel (1 * a) a

| mul_zero (a: Pre R α) : Rel (a * 0) 0
| zero_mul (a: Pre R α) : Rel (0 * a) 0

| add_assoc (a b c: Pre R α) : Rel ((a + b) + c) (a + (b + c))
| mul_assoc (a b c: Pre R α) : Rel ((a * b) * c) (a * (b * c))

| mul_add (k a b: Pre R α) : Rel (k * (a + b)) (k * a + k * b)
| add_mul (a b k: Pre R α) : Rel ((a + b) * k) (a * k + b * k)

| add_congr (a b c d: Pre R α) : Rel a c -> Rel b d -> Rel (a + b) (c + d)
| mul_congr (a b c d: Pre R α) : Rel a c -> Rel b d -> Rel (a * b) (c * d)

private instance setoid (R α: Type*) [SemiringOps R] : Setoid (Pre R α) where
  r := Rel
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }

end FreeAlgebra

structure FreeAlgebra (R α: Type*) [SemiringOps R] [IsSemiring R] where
  ofQuot :: toQuot : Quotient (FreeAlgebra.setoid R α)

namespace FreeAlgebra

variable [SemiringOps R] [IsSemiring R]

private def mk : Pre R α -> FreeAlgebra R α := .ofQuot ∘ Quotient.mk _
private def liftQuot (f: Pre R α -> β) (h: ∀a b, a ≈ b -> f a = f b) (a: FreeAlgebra R α) : β :=
  a.toQuot.lift f h
private def lift_mk (f: Pre R α -> β) (h: ∀a b, a ≈ b -> f a = f b) (a: Pre R α) : liftQuot f h (mk a) = f a := rfl
private def lift₂ (f: Pre R α -> Pre R α -> β) (h: ∀a b c d, a ≈ c -> b ≈ d -> f a b = f c d) (a: FreeAlgebra R α) (b: FreeAlgebra R α) : β :=
  a.toQuot.lift₂ f h b.toQuot
private def lift₂_mk (f: Pre R α -> β) (h: ∀a b, a ≈ b -> f a = f b) (a: Pre R α) : liftQuot f h (mk a) = f a := rfl
private def ind {motive: FreeAlgebra R α -> Prop} (mk: ∀a, motive (mk a)) (a: FreeAlgebra R α) : motive a := by
  obtain ⟨a⟩ := a
  induction a using Quotient.ind with | _ a =>
  exact mk a
private def ind₂ {motive: FreeAlgebra R α -> FreeAlgebra R α -> Prop} (mk: ∀a b, motive (mk a) (mk b)) (a b: FreeAlgebra R α) : motive a b := by
  induction a using ind with | _ a =>
  induction b using ind with | _ b =>
  apply mk
private def ind₃ {motive: FreeAlgebra R α -> FreeAlgebra R α -> FreeAlgebra R α -> Prop} (mk: ∀a b c, motive (mk a) (mk b) (mk c)) (a b c: FreeAlgebra R α) : motive a b c := by
  induction a using ind with | _ a =>
  induction b using ind with | _ b =>
  induction c using ind with | _ c =>
  apply mk
private def sound {a b: Pre R α} : a ≈ b -> mk a = mk b := by
  intro h
  show ofQuot _ = ofQuot _
  congr 1
  apply Quotient.sound
  assumption

def ι (R: Type*) [SemiringOps R] [IsSemiring R] : α -> FreeAlgebra R α := mk ∘ Pre.of

instance : Zero (FreeAlgebra R α) where
  zero := mk (.scalar 0)

instance : One (FreeAlgebra R α) where
  one := mk (.scalar 1)

instance : Add (FreeAlgebra R α) where
  add := lift₂ (fun a b => mk (.add a b)) <| by
    intro a b c d h g
    apply sound
    apply Rel.add_congr
    assumption
    assumption

instance : Mul (FreeAlgebra R α) where
  mul := lift₂ (fun a b => mk (.mul a b)) <| by
    intro a b c d h g
    apply sound
    apply Rel.mul_congr
    assumption
    assumption

instance : Pow (FreeAlgebra R α) ℕ where
  pow := flip fun n => liftQuot (fun a => mk (.npow a n)) <| by
    intro a b h
    dsimp
    replace h := sound h
    induction n with
    | zero =>
      rw [show mk (.npow _ 0) = 1 from ?_]
      rw [show mk (.npow _ 0) = 1 from ?_]
      apply sound
      apply Rel.npow_zero
      apply sound
      apply Rel.npow_zero
    | succ n ih =>
      rw [show mk (.npow a (n + 1)) = mk (.npow a n) * mk a from ?_]
      rw [show mk (.npow b (n + 1)) = mk (.npow b n) * mk b from ?_]
      congr 1
      apply sound
      apply Rel.npow_succ
      apply sound
      apply Rel.npow_succ

instance : SMul ℕ (FreeAlgebra R α) where
  smul n := liftQuot (fun a => mk (.nsmul n a)) <| by
    intro a b h
    dsimp
    replace h := sound h
    induction n with
    | zero =>
      rw [show mk (.nsmul 0 _) = 0 from ?_]
      rw [show mk (.nsmul 0 _) = 0 from ?_]
      apply sound
      apply Rel.zero_nsmul
      apply sound
      apply Rel.zero_nsmul
    | succ n ih =>
      rw [show mk (.nsmul (n + 1) a) = mk (.nsmul n a) + mk a from ?_]
      rw [show mk (.nsmul (n + 1) b) = mk (.nsmul n b) + mk b from ?_]
      congr 1
      apply sound
      apply Rel.succ_nsmul
      apply sound
      apply Rel.succ_nsmul

instance : NatCast (FreeAlgebra R α) where
  natCast n := .mk (.scalar n)

private def _algebraMap (R: Type*) [SemiringOps R] [IsSemiring R] : R →+* FreeAlgebra R α where
  toFun := .mk ∘ .scalar
  map_zero := rfl
  map_one := rfl
  map_add a b := by
    apply sound
    apply Rel.scalar_add
  map_mul a b := by
    apply sound
    apply Rel.scalar_mul

instance : AlgebraMap R (FreeAlgebra R α) where
  toAlgebraMap := _algebraMap R

instance : SMul R (FreeAlgebra R α) where
  smul r a := algebraMap R r * a

instance : IsSemiring (FreeAlgebra R α) where
  add_assoc a b c := by
    induction a, b, c using ind₃ with | _ =>
    apply sound
    apply Rel.add_assoc
  mul_assoc a b c := by
    induction a, b, c using ind₃ with | _ =>
    apply sound
    apply Rel.mul_assoc
  zero_add a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.zero_add
  add_zero a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.add_zero
  one_mul a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.one_mul
  mul_one a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.mul_one
  zero_mul a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.zero_mul
  mul_zero a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.mul_zero
  add_mul a b c := by
    induction a, b, c using ind₃ with | _ =>
    apply sound
    apply Rel.add_mul
  mul_add a b c := by
    induction a, b, c using ind₃ with | _ =>
    apply sound
    apply Rel.mul_add
  zero_nsmul a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.zero_nsmul
  succ_nsmul n a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.succ_nsmul
  npow_zero a := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.npow_zero
  npow_succ a n := by
    induction a using ind with | _ =>
    apply sound
    apply Rel.npow_succ
  natCast_zero := by
    show mk _ = mk _
    rw [natCast_zero]
  natCast_one := by
    show mk _ = mk _
    rw [natCast_one]
  natCast_succ n := by
    apply sound
    rw [natCast_succ]
    apply Rel.scalar_add

instance : IsAlgebra R (FreeAlgebra R α) where
  commutes r a := by
    induction a using ind with | _ a =>
    apply sound
    apply Rel.central
  smul_def _ _ := rfl

variable
  [SemiringOps A] [IsSemiring A] [AlgebraMap R A]
  [SMul R A] [IsAlgebra R A]

@[induction_eliminator]
def induction
  {motive: FreeAlgebra R α -> Prop}
  (algebraMap: ∀r: R, motive (algebraMap R r))
  (ι: ∀a: α, motive (ι R a))
  (add: ∀a b: FreeAlgebra R α, motive a -> motive b -> motive (a + b))
  (mul: ∀a b: FreeAlgebra R α, motive a -> motive b -> motive (a * b)):
  ∀a, motive a := by
  intro a
  induction a using ind with | _ a =>
  induction a with
  | scalar => apply algebraMap
  | of a => apply ι
  | add a b iha ihb =>
    apply add (mk a) (mk b)
    assumption
    assumption
  | mul a b iha ihb =>
    apply mul (mk a) (mk b)
    assumption
    assumption
  | nsmul n a ih =>
    show motive (n • mk a)
    induction n with
    | zero =>
      rw [zero_nsmul, ←map_zero (_root_.algebraMap R)]
      apply algebraMap
    | succ n ihn =>
      rw [succ_nsmul]
      apply add
      assumption
      assumption
  | npow a n ih =>
    show motive (mk a ^ n)
    induction n with
    | zero =>
      rw [npow_zero, ←map_one (_root_.algebraMap R)]
      apply algebraMap
    | succ n ihn =>
      rw [npow_succ]
      apply mul
      assumption
      assumption


private def Pre.lift (f: α -> A) : Pre R α -> A
| .of a => f a
| .scalar r => algebraMap R r
| .npow a n => lift f a ^ n
| .nsmul n a => n • lift f a
| .mul a b => lift f a * lift f b
| .add a b => lift f a + lift f b

private def preLift (f: α -> A) : FreeAlgebra R α →ₐ[R] A where
  toFun := liftQuot (Pre.lift f) <| by
    intro a b h
    induction h with
    | refl => rfl
    | symm => symm; assumption
    | trans _ _ iha ihb => rw [iha, ihb]
    | scalar_add => apply map_add (algebraMap R)
    | scalar_mul => apply map_mul (algebraMap R)
    | central => apply IsAlgebra.commutes
    | zero_nsmul a =>
      apply Eq.trans
      apply zero_nsmul (α := A)
      symm; apply map_zero (algebraMap R)
    | succ_nsmul => apply succ_nsmul (α := A)
    | npow_zero =>
      apply Eq.trans
      apply npow_zero (α := A)
      symm; apply map_one (algebraMap R)
    | npow_succ => apply npow_succ (α := A)
    | add_zero a =>
      show Pre.lift _ a + algebraMap R 0 = _
      rw [map_zero, add_zero]
    | zero_add a =>
      show algebraMap R 0 + Pre.lift _ a = _
      rw [map_zero, zero_add]
    | mul_one =>
      show Pre.lift _ _ * algebraMap R 1 = _
      rw [map_one, mul_one]
    | one_mul =>
      show algebraMap R 1 * Pre.lift _ _ = _
      rw [map_one, one_mul]
    | mul_zero =>
      show Pre.lift _ _ * algebraMap R 0 = algebraMap R 0
      rw [map_zero, mul_zero]
    | zero_mul =>
      show algebraMap R 0 * Pre.lift _ _ = algebraMap R 0
      rw [map_zero, zero_mul]
    | add_assoc => apply add_assoc
    | mul_assoc => apply mul_assoc
    | mul_add => apply mul_add
    | add_mul => apply add_mul
    | add_congr =>
      show Pre.lift _ _ + Pre.lift _ _ = Pre.lift _ _ + Pre.lift _ _
      congr
    | mul_congr =>
      show Pre.lift _ _ * Pre.lift _ _ = Pre.lift _ _ * Pre.lift _ _
      congr
  map_zero := map_zero (algebraMap R)
  map_one := map_one (algebraMap R)
  map_add a b := by
    induction a, b using ind₂ with | _ =>
    rfl
  map_mul a b := by
    induction a, b using ind₂ with | _ =>
    rfl
  map_smul r a := by
    induction a using ind with | _ =>
    show algebraMap R r * Pre.lift _ _ = _
    rw [smul_def]
    rfl

private def preLift_algebraMap (f: α -> A) : preLift (R := R) f (algebraMap R r) = algebraMap R r := rfl

def lift : (α -> A) ≃ (FreeAlgebra R α →ₐ[R] A) where
  toFun := preLift
  invFun f := f ∘ ι R
  leftInv := by
    intro f
    ext x
    induction x with
    | algebraMap r => rw [preLift_algebraMap, map_algebraMap]
    | ι x => rfl
    | add a b iha ihb => rw [map_add, map_add]; congr
    | mul => rw [map_mul, map_mul]; congr
  rightInv := by
    intro f
    ext x
    rfl

@[simp] def lift_ι (f: α -> A) (x: α) : lift f (ι R x) = f x := rfl

attribute [irreducible] ι _algebraMap lift

end FreeAlgebra
