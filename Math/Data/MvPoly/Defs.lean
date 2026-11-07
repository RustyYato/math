module

public import Math.Algebra.DirectSum.Defs
public import Math.Algebra.Algebra.Defs

namespace Math

public structure MvPoly (ι R: Type*) [SemiringOps R] [IsSemiring R] where
  ofDirectSum :: toDirectSum : ⊕_: (⊕_: ι, ℕ), R

namespace MvPoly

variable {ι α: Type*} [SemiringOps α] [IsSemiring α]

public instance : Zero (MvPoly ι α) where
  zero := ⟨0⟩
public instance : One (MvPoly ι α) where
  one := ⟨1⟩
public instance : Add (MvPoly ι α) where
  add a b := ⟨a.toDirectSum + b.toDirectSum⟩
public instance : Mul (MvPoly ι α) where
  mul a b := ⟨a.toDirectSum * b.toDirectSum⟩

@[expose]
public def eqv : (⊕_: (⊕_: ι, ℕ), α) ≃+* MvPoly ι α where
  toFun := ofDirectSum
  invFun := toDirectSum
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_mul _ _ := rfl

public instance [SMul S α] [IsLawfulSMulZero S α] [IsRightDistribSMul S α] : SMul S (MvPoly ι α) where
  smul s a := ⟨s • a.toDirectSum⟩
public instance : Pow (MvPoly ι α) ℕ where
  pow a n := ⟨a.toDirectSum ^ n⟩

public instance : NatCast (MvPoly ι α) where
  natCast n := ⟨n⟩

public instance instSemiringOps : SemiringOps (MvPoly ι α) := inferInstance
public instance instIsSemiring : IsSemiring (MvPoly ι α) :=
  OfEquiv.instIsSemiring eqv.toEquiv


public instance [SMul S α] [IsLawfulSMulZero S α] [IsRightDistribSMul S α] : IsLawfulSMulZero S (MvPoly ι α) where
  smul_zero r := by
    show eqv (r • 0) = _
    rw [smul_zero]; rfl
public instance [SMul S α] [IsLawfulSMulZero S α] [IsRightDistribSMul S α] : IsRightDistribSMul S (MvPoly ι α) where
  smul_add r a b := by
    show eqv (r • (a.toDirectSum + b.toDirectSum)) = _
    rw [smul_add]; rfl

public def term (i: ⊕_: ι, ℕ) : α →+ MvPoly ι α :=
  eqv.toAddGroupHom.comp (DirectSum.ι (R := fun _ => α) i)

public theorem term_mul_term (i j: ⊕_: ι, ℕ) (a b: α) :
  term i a * term j b = term (i + j) (a * b) := by
  apply eqv.symm.inj
  apply DirectSum.ι_mul_ι

public theorem smul_term
  [SMul S α] [IsLawfulSMulZero S α] [IsRightDistribSMul S α]
  (s: S) (i: ⊕_: ι, ℕ) (a: α) :
  s • term i a = term i (s • a) := by
  apply eqv.symm.inj
  apply DirectSum.smul_ι

public theorem add_induction
  {motive: MvPoly ι α -> Prop}
  (zero: motive 0)
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (term: ∀i a, motive (term i a))
  (poly: MvPoly ι α) : motive poly := by
  obtain ⟨poly⟩ := poly
  induction poly with
  | zero => apply zero
  | add => apply add <;> assumption
  | ι => apply term

instance [IsComm α] : IsComm (MvPoly ι α) where
  mul_comm a b := by
    induction a using add_induction with
    | zero => rw [mul_zero, zero_mul]
    | add => rw [add_mul, mul_add]; congr
    | term =>
    induction b using add_induction with
    | zero => rw [mul_zero, zero_mul]
    | add => rw [add_mul, mul_add]; congr
    | term => rw [term_mul_term, term_mul_term, add_comm, mul_comm]

public instance : AlgebraMap α (MvPoly ι α) where
  toAddGroupHom := term 0
  map_one := by rfl
  map_mul a b := by
    show term 0 (a * b) = term 0 a * term 0 b
    rw [term_mul_term, add_zero]

@[expose] public def X (i: ι) := term (.ι i 1) (1: α)

@[induction_eliminator]
public theorem induction
  {motive: MvPoly ι α -> Prop}
  (algebraMap: ∀a: α, motive (algebraMap α a))
  (X: ∀i, motive (X (α := α) i))
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (poly: MvPoly ι α): motive poly := by
  induction poly using add_induction with
  | zero =>
    rw [←map_zero (Math.algebraMap α)]
    apply algebraMap
  | add => apply add <;> assumption
  | term i a =>
    rw [←mul_one a, ←zero_add i, ←term_mul_term]
    apply mul; apply algebraMap
    clear a
    induction i with
    | zero => apply algebraMap 1
    | add a b iha ihb =>
      rw [←mul_one 1, ←term_mul_term]
      apply mul <;> assumption
    | ι i n =>
      -- show X ^ n
      induction n with
      | zero =>
        rw [map_zero]
        apply algebraMap
      | succ n ih =>
        rw [←mul_one (1: α), map_add, ←term_mul_term]
        apply mul
        assumption
        apply X

variable {R: Type*} [SemiringOps R] [IsSemiring R] [IsComm R]
  [SMul α R] [AlgebraMap α R] [IsAlgebra α R]

attribute [local irreducible] AddOfMul

def evalMonomial (f: ι -> R) : (⊕_: ι, ℕ) →+ AddOfMul R :=
  DirectSum.liftAdd fun i => {
      toFun n := n • AddOfMul.mk (f i)
      map_zero := by rw [zero_smul]
      map_add a b := by rw [add_smul]
    }

theorem evalMonomial_ι (f: ι -> R) (i: ι) (n: ℕ) :
  evalMonomial f (.ι i n) = AddOfMul.mk (f i ^ n) := by
  show DirectSum.liftAdd _ _ = _
  rw [DirectSum.liftAdd_ι]
  rfl

def preEvalAdd (f: ι -> R) : MvPoly ι α →+ R :=
  (AddGroupHom.comp · eqv.symm.toAddGroupHom) <|
    DirectSum.liftAdd fun i => {
      toFun a := a • AddOfMul.get (evalMonomial f i)
      map_zero := by rw [zero_smul]
      map_add a b := by rw [add_smul]
    }

theorem preEvalAdd_term (f: ι -> R) (i: ⊕_: ι, ℕ)  (val: α) :
  preEvalAdd f (term i val) = val • AddOfMul.get (evalMonomial f i) := by
  apply DirectSum.liftAdd_ι

variable [IsComm α]

instance : IsAlgebra α (MvPoly ι α) where
  commutes _ _ := mul_comm _ _
  smul_def k a := by
    induction a using add_induction with
    | zero => rw [smul_zero, mul_zero]
    | add => rw [smul_add, mul_add]; congr
    | term =>
      show _ = term _ _ * _
      rw [smul_term, term_mul_term, zero_add]
      rfl

def preEval (f: ι -> R) : MvPoly ι α →ₐ[α] R where
  toAddGroupHom := preEvalAdd f
  map_one := by
    show preEvalAdd f (term _ 1) = 1
    rw [preEvalAdd_term, one_smul, map_zero]
    rfl
  map_smul := by
    intro k a; show preEvalAdd _ _ = k • preEvalAdd _ a
    induction a using add_induction with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add a b iha ihb => rw [smul_add, map_add, iha, ihb, map_add, smul_add]
    | term i a => rw [smul_term, preEvalAdd_term, preEvalAdd_term, smul_assoc]
  map_mul a b := by
    show preEvalAdd _ _ = preEvalAdd _ a * preEvalAdd _ b
    induction a using add_induction with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | add x y ihx ihy => simp [add_mul, map_add, ihx, ihy]
    | term i a =>
      induction b using add_induction with
      | zero => simp [mul_zero, map_zero]
      | add x y ihx ihy => simp [mul_add, map_add, ihx, ihy]
      | term j b =>
        simp [term_mul_term,preEvalAdd_term]
        rw [smul_def a, smul_def b,
          mul_assoc, ←mul_assoc _ (algebraMap α b),
          mul_comm _ (algebraMap α b),
          mul_assoc, ←mul_assoc, ←map_mul, ←smul_def,
          map_add]
        rfl

theorem preEval_term (f: ι -> R) (i: ⊕_: ι, ℕ)  (val: α) :
  preEval f (term i val) = val • AddOfMul.get (evalMonomial f i) := by
  apply preEvalAdd_term

public def eval : (ι -> R) ≃ (MvPoly ι α →ₐ[α] R) where
  toFun := preEval
  invFun f i := f (term (.ι i 1) 1)
  leftInv f := by
    ext a; induction a using add_induction with
    | zero => rw [map_zero, map_zero]
    | add a b iha ihb => simp [map_add, iha, ihb]
    | term i a =>
      rw [preEval_term]; dsimp
      rw (occs := [2]) [←mul_one a]
      rw [←smul_eq_mul, ←smul_term, map_smul]
      congr
      induction i with
      | zero =>
        show _ = f 1
        rw [map_zero, map_one]; rfl
      | add i j ihi ihj =>
        rw [map_add]
        show (evalMonomial (R := R) _ i).get * (evalMonomial (R := R) _ j).get = _
        rw [ihi, ihj, ←map_mul, term_mul_term, one_mul]
      | ι i n =>
        rw [evalMonomial_ι, ←map_pown]; dsimp
        congr
        induction n with
        | zero =>
          rw [pown_zero, map_zero]
          rfl
        | succ n ih =>
          rw [map_add, pown_succ, ih,
            term_mul_term, mul_one]
  rightInv f := by
    ext i; dsimp
    rw [preEval_term, one_smul,
      evalMonomial_ι, pown_one]
    rfl

public theorem eval_X (f: ι -> R) (i: ι) : eval f (X (α := α) i) = f i := by
  show preEval _ (term _ _) = _
  rw [preEval_term, evalMonomial_ι, pown_one, one_smul]; rfl

end MvPoly
