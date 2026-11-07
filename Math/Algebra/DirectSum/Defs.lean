module

public import Math.Data.FreeMonoid.Defs
public import Math.Algebra.GroupQuot.Defs
public import Math.Algebra.Monoid.Action.Defs
public import Math.Algebra.GradedMonoid.Defs
public import Math.Algebra.Semiring.Defs

namespace Math

section

public instance [Add ι] [Mul α] [Add α] [IsLeftDistrib α]  : IsGradedLeftDistrib (fun _: ι => α) where
  gmul_add := mul_add
public instance [Add ι] [Mul α] [Add α] [IsRightDistrib α]  : IsGradedRightDistrib (fun _: ι => α) where
  add_gmul := add_mul

end

section Defs

variable {α: Type*} (R: α -> Type*)

public inductive DirectSum.Rel [∀a, Zero (R a)] [∀a, Add (R a)]
  : FreeAddMonoid (GradedMonoid R) -> FreeAddMonoid (GradedMonoid R) -> Prop where
| ι_add_ι : Rel (.ι ⟨a, x⟩ + .ι ⟨a, y⟩) (.ι ⟨a, x + y⟩)
| ι_zero_eq_zero : Rel (.ι ⟨a, 0⟩) 0
| comm (a b: FreeAddMonoid (GradedMonoid R)
) : Rel (a + b) (b + a)

public structure DirectSum [∀a, Zero (R a)] [∀a, Add (R a)] where
  ofQuot :: toQuot : AddGroupQuot (DirectSum.Rel R)

section Syntax

open Lean
open TSyntax.Compat

macro "⊕ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``DirectSum xs b

@[app_unexpander DirectSum] public meta def unexpand_DirectSum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ⊕ $xs:binderIdent*, $b) => `(⊕ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⊕ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⊕ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax

end Defs

namespace DirectSum

variable {α: Type*} {R: α -> Type*}

section AddMonoidOps

public instance
  instSMul
  [∀a, SMul S (R a)] [∀a, Zero (R a)] [∀a, Add (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  : SMul S (⊕a, R a) where
  smul n a := ofQuot (
    a.toQuot.lift <| {
      val := (AddGroupQuot.mk _).comp (FreeAddMonoid.lift (fun a => FreeAddMonoid.ι ⟨a.1, n • a.2⟩))
      property := by
        intro a b h; dsimp
        cases h with
        | ι_add_ι =>
          apply AddGroupQuot.sound
          rw [map_add]
          iterate 3 rw [FreeAddMonoid.lift_ι]
          dsimp
          rw [smul_add]
          apply Rel.ι_add_ι
        | ι_zero_eq_zero =>
          apply AddGroupQuot.sound
          rw [FreeAddMonoid.lift_ι]
          dsimp; rw [smul_zero, map_zero]
          apply Rel.ι_zero_eq_zero
        | comm =>
          apply AddGroupQuot.sound
          rw [map_add, map_add]
          apply Rel.comm
    }
  )

public instance [∀a, Zero (R a)] [∀a, Add (R a)] : Zero (⊕a, R a) where
  zero := ⟨0⟩
public instance [∀a, Zero (R a)] [∀a, Add (R a)] : Add (⊕a, R a) where
  add a b := ⟨a.toQuot + b.toQuot⟩
public instance [∀a, AddMonoidOps (R a)] [∀a, IsAddMonoid (R a)] [∀a, IsAddComm (R a)] : SMul ℕ (⊕a, R a) := inferInstance

end AddMonoidOps

section Ind

variable [∀a, Zero (R a)] [∀a, Add (R a)]

@[expose] public def eqv : AddGroupQuot (Rel R) ≃+ ⊕a, R a where
  toFun := ofQuot
  invFun := toQuot
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_add _ _ := rfl

public def ι (a: α) : R a →+ ⊕a, R a where
  toFun := eqv ∘ (AddGroupQuot.mk _) ∘ FreeAddMonoid.ι ∘ GradedMonoid.mk a
  map_zero := by
    dsimp; show eqv _ = eqv 0; congr
    apply AddGroupQuot.sound
    apply Rel.ι_zero_eq_zero
  map_add a b := by
    dsimp; show eqv _ = eqv (AddGroupQuot.mk _ _ + AddGroupQuot.mk _ _); congr
    symm; apply AddGroupQuot.sound
    apply Rel.ι_add_ι

public theorem eqv_symm_ι (r: R a) : eqv.symm (ι a r) = AddGroupQuot.mk _ (FreeAddMonoid.ι ⟨a ,r⟩) := by rfl

public theorem congr_ι
  (i j: α) (a: R i) (b: R j) (hi: i = j) (h: a ≍ b) : ι i a = ι j b := by
    cases hi; cases h; rfl

@[induction_eliminator]
public theorem induction
  {motive: (⊕a, R a) -> Prop}
  (zero: motive 0)
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (ι: ∀a (r: R a), motive (ι a r))
  (d: ⊕a, R a) : motive d := by
  obtain ⟨d⟩ := d
  induction d with | mk d =>
  induction d with
  | zero => apply zero
  | add => apply add ⟨AddGroupQuot.mk _ _⟩ ⟨AddGroupQuot.mk _ _⟩ <;> assumption
  | ι a => apply ι

end Ind

section AddMonoid

public instance
  [∀a, SMul S (R a)] [∀a, Zero (R a)] [∀a, Add (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  : IsLawfulSMulZero S (⊕a, R a) where
  smul_zero r := by
    show eqv (AddGroupQuot.lift _ 0) = eqv _
    rw [map_zero]
public instance
  [∀a, SMul S (R a)] [∀a, Zero (R a)] [∀a, Add (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  : IsRightDistribSMul S (⊕a, R a) where
  smul_add r a b := by
    obtain ⟨a⟩ := a
    obtain ⟨b⟩ := b
    show eqv (AddGroupQuot.lift _ (a + b)) = eqv _
    rw [map_add]
    rfl

public theorem smul_ι
  [∀a, SMul S (R a)] [∀a, Zero (R a)] [∀a, Add (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  (s: S) (r: R a) : s • ι a r = ι a (s • r) := by
  show eqv (AddGroupQuot.lift _ (AddGroupQuot.mk _ _)) = eqv _
  rw [AddGroupQuot.lift_mk]
  show eqv (AddGroupQuot.mk _ (FreeAddMonoid.lift _ (FreeAddMonoid.ι _))) = eqv _
  rw [FreeAddMonoid.lift_ι]
  rfl

variable [∀a, AddMonoidOps (R a)] [∀a, IsAddMonoid (R a)] [∀a, IsAddComm (R a)]

public instance: IsLawfulZero (⊕a, R a) :=
  OfEquiv.instIsLawfulZero eqv.toEquiv
public instance: IsAddSemigroup (⊕a, R a) :=
  OfEquiv.instIsAddSemigroup eqv.toEquiv
public instance: IsAddComm (⊕a, R a) where
  add_comm a b := by
    obtain ⟨a⟩ := a; obtain ⟨b⟩ := b
    show eqv (a + b) = eqv (b + a); congr 1
    induction a with | _ a =>
    induction b with | _ b =>
    apply AddGroupQuot.sound
    apply Rel.comm

public instance
  [Zero S]
  [∀a, SMul S (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  [∀a, IsLawfulZeroSMul S (R a)]
  : IsLawfulZeroSMul S (⊕a, R a) where
  zero_smul a := by
    induction a with
    | zero => rw [smul_zero]
    | add a b iha ihb => rw [smul_add, iha, ihb, add_zero]
    | ι a r => rw [smul_ι, zero_smul, map_zero]

public instance
  [One S]
  [∀a, SMul S (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  [∀a, IsLawfulOneSMul S (R a)]
  : IsLawfulOneSMul S (⊕a, R a) where
  one_smul a := by
    induction a with
    | zero => rw [smul_zero]
    | add a b iha ihb => rw [smul_add, iha, ihb]
    | ι a r => rw [smul_ι, one_smul]

public instance
  [Add S]
  [∀a, SMul S (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  [∀a, IsLeftDistribSMul S (R a)]
  : IsLeftDistribSMul S (⊕a, R a) where
  add_smul s₀ s₁ a := by
    induction a with
    | zero => rw [smul_zero, smul_zero, smul_zero, add_zero]
    | add a b iha ihb => rw [
      smul_add, iha, ihb,
      add_assoc, ←add_assoc (s₁ • a),
      add_comm (s₁ • a), add_assoc, ←add_assoc (s₀ • a),
      smul_add, smul_add]
    | ι a r => rw [smul_ι, add_smul, map_add, smul_ι, smul_ι]

public instance
  [Mul S]
  [∀a, SMul S (R a)]
  [∀a, IsLawfulSMulZero S (R a)] [∀a, IsRightDistribSMul S (R a)]
  [∀a, IsLawfulMulSMul S (R a)]
  : IsLawfulMulSMul S (⊕a, R a) where
  mul_smul s₀ s₁ a := by
    induction a with
    | zero => rw [smul_zero, smul_zero, smul_zero]
    | add a b iha ihb => rw [smul_add, iha, ihb, smul_add, smul_add]
    | ι a r => rw [smul_ι, mul_smul, smul_ι, smul_ι]

public instance: IsAddMonoid (⊕a, R a) where
  zero_nsmul a := by
    induction a with rw [zero_smul]
  succ_nsmul a n := by rw [add_smul, one_smul]

section Lift

variable [AddMonoidOps M] [IsAddMonoid M] [IsAddComm M]

def preLift (f: ∀a, R a →+ M) : (⊕a, R a) →+ M :=
  -- this inferInstance is to pull in all relevant
  -- preconditions on `R` for add monoid
  have : IsAddMonoid (⊕a, R a) := inferInstance
  (AddGroupHom.comp · eqv.symm.toAddGroupHom) <| AddGroupQuot.lift {
    val := FreeAddMonoid.lift (fun x => f x.1 x.2)
    property := by
      intro a b h; cases h with
      | comm => simp [map_add, add_comm]
      | ι_add_ι => simp [FreeAddMonoid.lift_ι, map_add]
      | ι_zero_eq_zero => simp [FreeAddMonoid.lift_ι, map_zero]
  }

theorem preLift_ι (f: ∀a, R a →+ M) (a: α) (r: R a) : preLift f (ι a r) = f a r := by
  unfold preLift; simp [eqv_symm_ι, AddGroupQuot.lift_mk, FreeAddMonoid.lift_ι]

public def liftAdd : (∀a, R a →+ M) ≃ (⊕a, R a) →+ M where
  toFun := preLift
  invFun f a := f.comp (ι a)
  leftInv f := by
    ext d; induction d with
    | zero => simp [map_zero]
    | add a b iha ihb => simp [map_add, iha, ihb]
    | ι => simp [preLift_ι]
  rightInv f := by ext a r; simp [preLift_ι]

public theorem liftAdd_ι (f: ∀a, R a →+ M) (a: α) (r: R a) : liftAdd f (ι a r) = f a r := preLift_ι _ _ _

end Lift

end AddMonoid

section Mul

public instance [Zero α] [One (R 0)]
  [∀a, Zero (R a)] [∀a, Add (R a)] : One (⊕a, R a) where
  one := ι 0 1

public theorem one_eq
  [Zero α] [One (R 0)]
  [∀a, Zero (R a)] [∀a, Add (R a)] :
  (1: ⊕a, R a) = ι (0: α) (1: R 0) := rfl

variable
  [∀a, AddMonoidOps (R a)] [∀a, IsAddMonoid (R a)] [∀a, IsAddComm (R a)]
  [Add α] [GradedMul R] [IsLawfulGradedZeroMul R]
  [IsGradedLeftDistrib R] [IsGradedRightDistrib R]

section

public def mulHom : (⊕a, R a) →+ (⊕a, R a) →+ (⊕a, R a) :=
  liftAdd <| fun i => {
    toFun a := liftAdd <| fun j => {
      toFun b := ι _ (a * b)
      map_zero := by rw [gmul_zero, map_zero]
      map_add x y := by rw [gmul_add, map_add]
    }
    map_zero := by
      ext d; simp [zero_gmul, map_zero]
      induction d with
      | zero => simp [map_zero]
      | add a b iha ihb => simp [map_add, iha, ihb, add_zero]
      | ι a r => rw [liftAdd_ι]; rfl
    map_add x y := by
      ext d; simp [add_gmul, map_add]
      induction d with
      | zero => simp [map_zero, add_zero]
      | add a b iha ihb =>
        simp [map_add, iha, ihb]
        repeat rw [add_assoc]
        congr 1; rw [←add_assoc _ (liftAdd _ a),
          add_comm _ (liftAdd _ a), add_assoc]
      | ι a r =>
        simp [liftAdd_ι]
        rfl
  }

public instance : Mul (⊕a, R a) where
  mul a b := mulHom a b

public instance : IsLeftDistrib (⊕a, R a) where
  mul_add k a b := by
    show mulHom _ _ = mulHom _ _ + mulHom _ _
    rw [map_add]
public instance : IsRightDistrib (⊕a, R a) where
  add_mul a b k := by
    show mulHom _ _ = mulHom _ _ + mulHom _ _
    rw [map_add]; rfl
public instance : IsLawfulZeroMul (⊕a, R a) where
  mul_zero a := by
    show mulHom _ _ = _
    rw [map_zero]
  zero_mul a := by
    show mulHom _ _ = _
    rw [map_zero]; rfl

public theorem ι_mul_ι (a: R i) (b: R j) : ι i a * ι j b = ι (i + j) (a * b) := by
  show mulHom _ _ = _
  unfold mulHom
  simp [liftAdd_ι]
  show liftAdd _ _ = _
  rw [liftAdd_ι]
  rfl

public instance [Zero α] [One (R 0)] [IsLawfulZero α] [IsLawfulGradedOne R] : IsLawfulOne (⊕a, R a) where
  one_mul a := by
    rw [one_eq]; induction a with
    | zero => rw [mul_zero]
    | add a b iha ihb => rw [mul_add, iha ,ihb]
    | ι a r =>
      rw [ι_mul_ι]; congr
      any_goals rw [zero_add]
      apply gone_gmul
  mul_one a := by
    rw [one_eq]; induction a with
    | zero => rw [zero_mul]
    | add a b iha ihb => rw [add_mul, iha, ihb]
    | ι a r =>
      rw [ι_mul_ι]; congr
      any_goals rw [add_zero]
      apply gmul_gone

public instance [IsAddSemigroup α] [IsGradedSemigroup R] : IsSemigroup (⊕a, R a) where
  mul_assoc a b c := by
    induction a generalizing b c with
    | zero => simp [zero_mul]
    | ι i a =>
      induction b generalizing c with
      | zero => simp [mul_zero, zero_mul]
      | ι j b =>
        rw [ι_mul_ι]
        induction c with
        | zero => simp [mul_zero]
        | ι k c =>
          iterate 3 rw [ι_mul_ι]
          apply congr_ι
          apply add_assoc
          apply gmul_assoc
        | add x y ihx ihy => simp [mul_add, ihx, ihy]
      | add x y ihx ihy => simp [mul_add, add_mul, ihx, ihy]
    | add x y ihx ihy => simp [add_mul, ihx, ihy]

end

section

variable
  [Zero α] [One (R 0)] [IsLawfulZero α] [IsLawfulGradedOne R]
  [IsAddSemigroup α] [IsGradedSemigroup R]

public instance : Pow (⊕a, R a) ℕ := DefaultPowN.instPowNat
public instance : IsLawfulPowN (⊕a, R a) := DefaultPowN.instIsLawfulPowN
public instance : IsMonoid (⊕a, R a) where

end

section

variable [Zero α] [One (R 0)] [NatCast (R 0)]

public instance : NatCast (⊕a, R a) where
  natCast n := ι 0 n

public instance [IsLawfulNatCast (R 0)] : IsLawfulNatCast (⊕a, R a) where
  natCast_zero := by
    show ι (0: α) ((0: ℕ): R 0) = _
    rw [natCast_zero, map_zero]
  natCast_succ n := by
    show ι 0 ((n + 1: ℕ): R 0) = _
    rw [natCast_succ, map_add]
    rfl

public instance [IsLawfulNatCast (R 0)] : IsAddMonoidWithOne (⊕a, R a) where

end

variable [IsAddSemigroup α] [IsGradedSemigroup R]

public instance : IsNonUnitalSemiring (⊕a, R a) where

variable [Zero α] [One (R 0)] [NatCast (R 0)] [IsLawfulNatCast (R 0)]
  [IsLawfulZero α] [IsLawfulGradedOne R]

public instance : IsSemiring (⊕a, R a) where

@[expose]
public def C : R 0 →+* ⊕a, R a where
  toAddGroupHom := ι 0
  map_one := rfl
  map_mul a b := by
    show ι 0 _ = ι 0 _ * ι 0 _
    rw [ι_mul_ι]; apply congr_ι
    rw [add_zero]
    apply cast_heq

end Mul

end DirectSum
