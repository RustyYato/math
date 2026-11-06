module

public import Math.Algebra.Algebra.Defs
public import Math.Algebra.Monoid.Action.Defs

namespace Math

public structure Poly.Spec (α: Type*) [Zero α] (toFun: ℕ -> α) where
  degree_p1: ℕ
  degree_p1_spec: ∀i, degree_p1 ≤ i -> toFun i = 0

public structure Poly (α: Type*) [SemiringOps α] [IsSemiring α] where
  toFun : ℕ -> α
  toSpec: Squash (Poly.Spec α toFun)

namespace Poly

scoped postfix:max "[X]" => Poly

variable [SemiringOps P] [IsSemiring P]

public instance : Funlike P[X] ℕ P where
  coeInj := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ h
    cases h; congr; apply Subsingleton.allEq

@[ext] theorem ext (a b: P[X]) (h: ∀i, a i = b i) : a = b := DFunlike.ext _ _ h

public instance : Zero P[X] where
  zero := {
    toFun _ := 0
    toSpec := Squash.mk {
      degree_p1 := 0
      degree_p1_spec _ _ := rfl
    }
  }

public instance : Add P[X] where
  add a b := {
    toFun i := a.toFun i + b.toFun i
    toSpec :=
      a.toSpec.recOnSubsingleton fun ha =>
      b.toSpec.recOnSubsingleton fun hb =>
      Squash.mk {
        degree_p1 := max ha.degree_p1 hb.degree_p1
        degree_p1_spec i hi := by
          rw [ha.degree_p1_spec, hb.degree_p1_spec, add_zero]
          omega
          omega
      }
  }

public instance [SMul α P] [IsLawfulSMulZero α P] : SMul α P[X] where
  smul b a := {
    toFun i := b • a.toFun i
    toSpec :=
      a.toSpec.recOnSubsingleton fun ha =>
      Squash.mk {
        degree_p1 := ha.degree_p1
        degree_p1_spec i hi := by
          rw [ha.degree_p1_spec i hi, smul_zero]
      }
  }

@[simp] theorem apply_zero (i: ℕ) : (0: P[X]) i = 0 := rfl
@[simp] theorem apply_add (a b: P[X]) (i: ℕ) : (a + b) i = a i + b i := rfl
@[simp] theorem apply_smul [SMul α P] [IsLawfulSMulZero α P] (b: α) (a: P[X]) (i: ℕ) : (b • a) i = b • a i := rfl

public instance : IsAddMonoid P[X] where
  add_assoc a b c := by ext; apply add_assoc
  add_zero a := by ext; apply add_zero
  zero_add a := by ext; apply zero_add
  zero_nsmul a := by ext; apply zero_nsmul
  succ_nsmul a n := by ext; apply succ_nsmul

public instance : IsAddComm P[X] where
  add_comm a b := by ext; apply add_comm

@[expose] public def monomial' (factor: P) (pow: ℕ) : P[X] where
  toFun i := if i = pow then factor else 0
  toSpec := .mk {
    degree_p1 := pow + 1
    degree_p1_spec i hi := by
      rw [ite_eq_right]
      intro rfl
      nomatch Nat.not_lt_of_le hi (Nat.lt_succ_self _)
  }

@[simp] theorem apply_monomial' (factor: P) (pow i: ℕ) :  monomial' factor pow i = if i = pow then factor else 0 := rfl

@[expose] public def monomial (pow: ℕ) : P →+ P[X] where
  toFun := (monomial' · pow)
  map_zero := by ext i; dsimp; split <;> rfl
  map_add a b := by ext i; dsimp; split; rfl; rw [add_zero]

@[simp] theorem apply_monomial (factor: P) (pow i: ℕ) :  monomial pow factor i = if i = pow then factor else 0 := rfl

@[expose] public def X : P[X] := monomial 1 1

public theorem list_add_induction
  {motive: P[X] -> Prop}
  (zero: motive 0)
  (add: ∀a n p, motive a -> motive (a + monomial n p ))
  (p: P[X]) : motive p := by
  obtain ⟨p, hp⟩ := p
  induction hp using Quotient.ind with | _ hp =>
  obtain ⟨deg, hp⟩ := hp
  induction deg generalizing p with
  | zero =>
    apply cast _ zero
    suffices p = fun _ => 0 by subst p; congr
    ext i; apply hp; apply Nat.zero_le
  | succ deg ih =>
    apply cast _ (add {
      toFun i := if i < deg then p i else 0
      toSpec := .mk {
        degree_p1 := deg
        degree_p1_spec := by
          intro i hi; rw [ite_eq_right]
          apply Nat.not_lt_of_le
          assumption
      }
    } deg (p deg) _)
    show motive (Poly.mk _ _) = _; dsimp
    suffices p = fun i => (if i < deg then p i else 0) + (monomial deg (p deg)) i by
      congr 2; symm; apply this
      apply Subsingleton.helim
      congr; symm; apply this
    ext i; dsimp
    split; rw [ite_eq_right, add_zero]
    omega; rw [zero_add]; split; congr
    apply hp; omega
    apply ih

public theorem add_induction
  {motive: P[X] -> Prop}
  (monomial: ∀n p, motive (monomial n p))
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (p: P[X]) : motive p := by
  induction p using list_add_induction with
  | zero =>
    rw [←map_zero (α := P) (Poly.monomial (P := P) 0)]
    apply monomial
  | add a n p ih =>
    apply add; assumption
    apply monomial

section

variable [AddMonoidOps G] [IsAddMonoid G] [IsAddComm G]

def monoid_fold [IsSemiring P] [IsAddMonoid G] [IsAddComm G] (f: ℕ -> P →+ G) (p: ℕ -> P) (deg: ℕ) : G :=
  Fin.foldr deg (fun i g => f i (p i) + g) 0

theorem monoid_fold_zero (f: ℕ -> P →+ G) (p: ℕ -> P) : monoid_fold f p 0 = 0 := rfl
theorem monoid_fold_succ (f: ℕ -> P →+ G) (p: ℕ -> P) (deg: ℕ) : monoid_fold f p (deg + 1) =
  f 0 (p 0) + monoid_fold (f ∘ Nat.succ) (p ∘ Nat.succ) deg := Fin.foldr_succ _ _
theorem monoid_fold_succ_last (f: ℕ -> P →+ G) (p: ℕ -> P) (deg: ℕ) : monoid_fold f p (deg + 1) =
  monoid_fold f p deg + f deg (p deg) := by
  induction deg generalizing f p with
  | zero => rw [monoid_fold_succ, monoid_fold_zero, monoid_fold_zero, add_zero, zero_add]
  | succ deg ih =>
    rw [monoid_fold_succ, ih, ←add_assoc, ←monoid_fold_succ]
    rfl

theorem monoid_fold_eq_zero' (f: ℕ -> P →+ G) (p: ℕ -> P) (deg: ℕ) (h: ∀i, i < deg -> p i = 0) : monoid_fold f p deg = 0 := by
  induction deg generalizing p f with
  | zero => rfl
  | succ deg_b ih =>
    rw [monoid_fold_succ, ih, add_zero, h, map_zero]; apply Nat.zero_lt_succ
    intro i hi; apply h; apply Nat.succ_lt_succ; assumption

theorem monoid_fold_eq_zero (f: ℕ -> P →+ G) (p: ℕ -> P) (deg: ℕ) (h: ∀i, p i = 0) : monoid_fold f p deg = 0 := by
  apply monoid_fold_eq_zero'
  intro i hi; apply h

theorem monoid_fold_add (f: ℕ -> P →+ G) (p q: ℕ -> P) (degp degq: ℕ)
  (hp: ∀i, degp ≤ i -> p i = 0) (hq: ∀i, degq ≤ i -> q i = 0)
   : monoid_fold f p degp + monoid_fold f q degq = monoid_fold f (fun i => p i + q i) (max degp degq) := by
  induction degp generalizing degq f p q with
  | zero =>
    rw [monoid_fold_zero, zero_add, Nat.zero_max]
    congr; ext i; rw [hp, zero_add]
    apply Nat.zero_le
  | succ degp ih =>
    cases degq with
    | zero =>
      rw [monoid_fold_zero, add_zero, Nat.max_zero]
      congr; ext i; rw [hq, add_zero]
      apply Nat.zero_le
    | succ degq =>
      rw [Nat.succ_max_succ, monoid_fold_succ, monoid_fold_succ, monoid_fold_succ]
      rw [←add_assoc, add_assoc (f 0 (p 0)), add_comm _ (f 0 (q 0)),
        ←add_assoc, map_add, add_assoc]; congr 1
      apply ih
      · intro i hi; apply hp
        apply Nat.succ_le_succ
        assumption
      · intro i hi; apply hq
        apply Nat.succ_le_succ
        assumption

def preLiftAdd (f: ℕ -> P →+ G) (p: P[X]) : G :=
  p.toSpec.liftOn (fun s => monoid_fold f p.toFun s.degree_p1) <| by
      intro ha hb h; clear h
      obtain ⟨p, h⟩ := p
      obtain ⟨deg_a, ha⟩ := ha
      obtain ⟨deg_b, hb⟩ := hb
      dsimp at ha hb; dsimp
      clear h
      induction deg_a generalizing deg_b p f with
      | zero =>
        rw [monoid_fold_zero, monoid_fold_eq_zero]
        intro i; apply ha
        apply Nat.zero_le
      | succ deg_a ih =>
        cases deg_b with
        | zero =>
          rw [monoid_fold_zero, monoid_fold_eq_zero]
          intro i; apply hb
          apply Nat.zero_le
        | succ deg_b =>
          rw [monoid_fold_succ, monoid_fold_succ]
          congr 1; apply ih
          · intro i hi; apply ha
            apply Nat.succ_le_succ; assumption
          · intro i hi; apply hb
            apply Nat.succ_le_succ; assumption

theorem preLiftAdd_monomial (f: ℕ -> P →+ G) (factor: P) (pow: ℕ) : preLiftAdd f (monomial pow factor) = f pow factor := by
  show monoid_fold _ (monomial pow factor) (pow + 1) = _
  rw [monoid_fold_succ_last, monoid_fold_eq_zero', zero_add]
  simp; intro i hi; simp;intro rfl; nomatch Nat.lt_irrefl _ hi

def preLiftAddHom (f: ℕ -> P →+ G) : P[X] →+ G where
  toFun := preLiftAdd f
  map_zero := rfl
  map_add a b := by
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    induction ha using Quotient.ind with | _ ha =>
    induction hb using Quotient.ind with | _ hb =>
    symm; apply monoid_fold_add
    apply ha.degree_p1_spec
    apply hb.degree_p1_spec

theorem preLiftAddHom_monomial (f: ℕ -> P →+ G) (factor: P) (pow: ℕ) : preLiftAddHom f (monomial pow factor) = f pow factor := by
  apply preLiftAdd_monomial

public def liftAdd : (ℕ -> P →+ G) ≃ (P[X] →+ G) where
  toFun := preLiftAddHom
  invFun f n := f.comp (monomial n)
  leftInv f := by
    ext p; dsimp
    induction p using add_induction with
    | monomial pow p => rw [preLiftAddHom_monomial]; rfl
    | add a b iha ihb => rw [map_add, map_add]; congr
  rightInv f := by
    ext n p; dsimp
    rw [preLiftAddHom_monomial]

public theorem liftAdd_monomial (f: ℕ -> P →+ G) (n: ℕ) (p: P) : liftAdd f (monomial n p) = f n p :=
  preLiftAdd_monomial _ _ _

end

@[expose] public def mulHom : P[X] →+ P[X] →+ P[X] :=
  liftAdd (fun i => {
    toFun a := liftAdd (fun j => {
      -- (a * X ^ i) * (b * X ^ j) = (a * b * X ^ (i + j))
      toFun b := monomial (i + j) (a * b)
      map_zero := by rw [mul_zero, map_zero]
      map_add x y := by rw [mul_add, map_add]
    })
    map_zero := by
      simp [zero_mul, map_zero]
      ext1 p; show liftAdd (fun _ => 0) p = 0
      induction p using add_induction with
      | monomial => rw [liftAdd_monomial]; rfl
      | add a b iha ihb => rw [map_add, iha, ihb, add_zero]
    map_add a b := by
      simp [add_mul, map_add]
      ext1 p
      induction p using add_induction with
      | monomial n p => simp [liftAdd_monomial]; rfl
      | add a b iha ihb => simp [map_add]; congr
  })

public instance : Mul P[X] where
  mul a b := mulHom a b
public instance : One P[X] where
  one := monomial 0 1

public instance : IsLeftDistrib P[X] where
  mul_add k a b := by apply map_add
public instance : IsRightDistrib P[X] where
  add_mul k a b := by
    show mulHom _ _ = mulHom _ _ + mulHom _ _
    rw [map_add]; rfl

@[simp] public theorem mul_monomial (i j: ℕ) (a b: P) : monomial i a * monomial j b = monomial (i + j) (a * b) := by
  show (mulHom _).toFun _ = _; dsimp [mulHom]
  rw [liftAdd_monomial]
  show liftAdd _ _ = _
  rw [liftAdd_monomial]
  rfl
public theorem one_eq : 1 = monomial 0 (1: P) := rfl

@[expose] public def C : P →+* P[X] where
  toAddGroupHom := monomial 0
  map_one := rfl
  map_mul a b := (mul_monomial 0 0 a b).symm

public instance : IsLawfulOne P[X] where
  mul_one a := by
    rw [one_eq]; induction a using add_induction with
    | monomial => rw [mul_monomial, mul_one, add_zero]
    | add => rw [add_mul]; congr
  one_mul a := by
    rw [one_eq]; induction a using add_induction with
    | monomial => rw [mul_monomial, one_mul, zero_add]
    | add => rw [mul_add]; congr

public instance : IsSemigroup P[X] where
  mul_assoc a b c := by
    induction a using add_induction generalizing b c with
    | monomial i a =>
      induction b using add_induction generalizing c with
      | monomial j b =>
        rw [mul_monomial]
        induction c using add_induction with
        | monomial k c => simp [mul_assoc, add_assoc]
        | add x y ihx ihy => simp [mul_add, ihx, ihy]
      | add x y ihx ihy => simp [mul_add, add_mul, ihx, ihy]
    | add x y ihx ihy => simp [add_mul, ihx, ihy]

public instance : Pow P[X] ℕ :=
  DefaultPowN.instPowNat
public instance : IsLawfulPowN P[X] :=
  DefaultPowN.instIsLawfulPowN

public instance : NatCast P[X] where
  natCast n := C n

public theorem natCast_eq (n: ℕ) : n = C (n: P) := rfl

public instance : IsSemiring P[X] where
  mul_zero a := by
    show mulHom _ _ = _
    rw [map_zero]
  zero_mul a := by
    show mulHom _ _ = _
    rw [map_zero]; rfl
  natCast_zero := by rw [natCast_eq, natCast_zero, map_zero]
  natCast_succ n := by
    rw [natCast_eq, natCast_succ, map_add]
    rfl

@[simp] public theorem monomial_zero (p: P) : monomial 0 p = C p := rfl
@[simp] public theorem monomial_succ (n: ℕ) (p: P) : monomial (n + 1) p = monomial n p * X := by
  unfold X; rw [mul_monomial, mul_one]
@[simp] public theorem monomial_succ' (n: ℕ) (p: P) : monomial (n + 1) p = X * monomial n p := by
  unfold X; rw [mul_monomial, one_mul, add_comm]

@[induction_eliminator]
public theorem induction
  {motive: P[X] -> Prop}
  (C: ∀p, motive (C p))
  (X: motive X)
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (p: P[X]) : motive p := by
  induction p using add_induction with
  | monomial n p =>
    induction n with
    | zero => apply C
    | succ n ih =>
      rw [monomial_succ]; apply mul; apply ih; apply X
  | add => apply add <;> assumption

public instance : AlgebraMap P P[X] where
  toRingHom := C

public theorem algebraMap_eq_C : algebraMap P = C := rfl

@[simp] public theorem smul_monomial [SMul S P] [IsLawfulSMulZero S P]
  (s: S) (n: ℕ) (p: P) : s • monomial n p = monomial n (s • p) := by
  ext i; dsimp; split; rfl; rw [smul_zero]

instance
  [SMul S P]
  [SemiringOps S] [IsSemiring S]
  [IsModule S P]
  : IsRightDistribSMul S P[X] where
  smul_add r a b := by ext i; simp ;rw [smul_add]

instance
  [SMul S P]
  [SemiringOps S] [IsSemiring S]
  [IsModule S P]
  : IsModule S P[X] where
  zero_smul _ := by ext i; simp; rw [zero_smul]
  smul_zero _ := by ext i; simp; rw [smul_zero]
  one_smul _ := by ext i; simp; rw [one_smul]
  mul_smul _ _ _ := by ext i; simp; rw [mul_smul]
  add_smul _ _ _ := by ext i; simp; rw [add_smul]
  smul_add _ _ _ := by ext i; simp; rw [smul_add]

variable [IsComm P]

public instance : IsComm P[X] where
  mul_comm a b := by
    induction a using add_induction generalizing b with
    | monomial =>
      induction b using add_induction with
      | monomial => rw [mul_monomial, mul_monomial, add_comm, mul_comm]
      | add =>
        rw [mul_add, add_mul]
        congr
    | add _ _ iha ihb => rw [mul_add, add_mul, iha, ihb]

public instance : IsAlgebra P P[X] where
  commutes _ _ := mul_comm _ _
  smul_def r p := by
    induction p using add_induction with
    | monomial =>
      rw [algebraMap_eq_C, ←monomial_zero, mul_monomial,
        zero_add]
      ext i; simp; split <;> rfl
    | add => rw [smul_add, mul_add]; congr

variable
  [SemiringOps S] [IsSemiring S]
  [SMul P S] [AlgebraMap P S] [IsAlgebra P S]

public def eval (s: S) [∀s', IsCommAt s s'] : P[X] →ₐ[P] S where
  toAddGroupHom := liftAdd fun n => {
    toFun p := p • s ^ n
    map_zero := by rw [zero_smul]
    map_add a b := by rw [add_smul]
  }
  map_smul k a := by
    show liftAdd _ _ = k • liftAdd _ _
    induction a using add_induction with
    | monomial n p =>
      simp [liftAdd_monomial]
      show (k • p) • s ^ n = k • (p • s ^ n)
      rw [smul_assoc]
    | add a b iha ihb => simp [map_add, smul_add, iha, ihb]
  map_one := by
    show liftAdd _ (monomial _ _) = _
    rw [liftAdd_monomial]
    show (1: P) • s ^ 0 = 1
    rw [one_smul, pown_zero]
  map_mul a b := by
    show liftAdd _ _ = liftAdd _ _ * liftAdd _ _
    induction a using add_induction generalizing b with
    | monomial i a =>
      induction b using add_induction with
      | monomial j b =>
        simp [mul_monomial, liftAdd_monomial]
        show (a * b) • s ^ (i + j) = a • s ^ i * b • s ^ j
        simp [smul_def]
        rw [mul_comm _ (s ^ j),
        mul_assoc, ←mul_assoc (s ^ i),
        ←pown_add,
        ←mul_assoc, mul_comm (algebraMap P a),
        mul_assoc, ←map_mul, mul_comm]
      | add a b iha ihb => rw [map_add, mul_add, map_add, iha, ihb, mul_add]
    | add a b iha ihb => simp [add_mul, map_add, iha, ihb]

public theorem eval_monomial (n: ℕ) (p: P) (s: S) [∀s', IsCommAt s s'] : eval s (monomial n p) = p • s ^ n := by
  apply liftAdd_monomial

public theorem eval_C (p: P) (s: S) [∀s', IsCommAt s s'] : eval s (C p) = algebraMap P p := by
  rw [←algebraMap_eq_C, map_algebraMap]

public theorem eval_X (s: S) [∀s', IsCommAt s s'] : eval s (.X: P[X]) = s := by
  unfold X; rw [eval_monomial, pown_one, one_smul]
