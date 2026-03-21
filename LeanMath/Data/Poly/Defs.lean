import LeanMath.Data.Fintype.Algebra.Monoid
import LeanMath.Algebra.Semiring.Char
import LeanMath.Algebra.Algebra.Defs
import LeanMath.Order.Defs
import LeanMath.Data.Trunc.Defs
import LeanMath.Logic.Funlike

structure Poly.DegreeRepr {P: Type*} [Zero P] (toFun: Nat -> P) : Type where
  degree_p1: ℕ
  spec: ∀x ≥ degree_p1, toFun x = 0

structure Poly (P: Type*) [Zero P] where
  toFun: ℕ -> P
  spec: Trunc (Poly.DegreeRepr toFun)

postfix:max "[X]" => Poly

namespace Poly

instance [Zero P] : FunLike P[X] ℕ P where
  coeInj := by
    intro a b h
    cases a; congr
    apply Subsingleton.helim
    congr

instance [Zero P] : Zero P[X] where
  zero := {
    toFun _ := 0
    spec := Trunc.mk {
      degree_p1 := 0
      spec _ _ := rfl
    }
  }

@[ext] def ext [Zero P] (a b: P[X]) : (∀i, a i = b i) -> a = b := DFunLike.ext _ _

@[simp] def apply_mk [Zero P] {toFun: ℕ -> P} {spec} : Poly.mk toFun spec i = toFun i := rfl
@[simp] def apply_zero [Zero P] : (0: P[X]) i = 0 := rfl
@[simp] def apply_toFun [Zero P] (a: P[X]) (i: ℕ) : a.toFun i = a i := rfl

variable [SemiringOps P] [IsSemiring P]

instance : Add P[X] where
  add a b := {
    toFun i := a.toFun i + b.toFun i
    spec :=
      a.spec.bind fun ha =>
      b.spec.map fun hb => {
        degree_p1 := ha.degree_p1 ⊔ hb.degree_p1
        spec := by
          intro x hx
          rw [ha.spec, hb.spec, add_zero]
          apply le_trans _ hx
          apply right_le_max
          apply le_trans _ hx
          apply left_le_max
      }
  }

@[simp] def apply_add (a b: P[X]) : (a + b) i = a i + b i := rfl

def term (degree: ℕ) : P →+ P[X] where
  toFun a := {
    toFun i := if i = degree then a else 0
    spec := Trunc.mk {
      degree_p1 := degree + 1
      spec := by
        intro x hx; rw [if_neg]
        apply Nat.ne_of_gt
        assumption
    }
  }
  map_zero := by
    ext i; dsimp
    split <;> rfl
  map_add a b := by
    ext i; dsimp
    split; rfl; rw [add_zero]

@[simp] def apply_term (degree i: ℕ) (val: P) : term degree val i = if i = degree then val else 0 := rfl

-- X is a single degree term with a coefficient of 1
def X : P[X] := term 1 1

instance [SMul R P] [IsLawfulSMulZero R P] : SMul R P[X] where
  smul r p := {
    toFun i := r • p.toFun i
    spec := p.spec.map fun hp => {
      degree_p1 := hp.degree_p1
      spec := by
        intro i hi
        rw [hp.spec _ hi, smul_zero]
    }
  }

instance : IsAddComm P[X] where
  add_comm _ _ := by ext i; apply add_comm

instance : IsAddMonoid P[X] where
  add_assoc _ _ _ := by ext i; apply add_assoc
  zero_add _ := by ext i; apply zero_add
  add_zero _ := by ext i; apply add_zero
  zero_nsmul _ := by ext i; apply zero_nsmul
  succ_nsmul _ _ := by ext i; apply succ_nsmul


private def erase (i: ℕ) (p: P[X]) : P[X] where
  toFun j := if j = i then 0 else p j
  spec := p.spec.map fun hp => {
    degree_p1 := hp.degree_p1
    spec := by
      intro x hx; split; rfl
      apply hp.spec
      assumption
  }

private def apply_erase (i j: ℕ) (p: P[X]) : p.erase i j = if j = i then 0 else p j := rfl

private def erase_add_term (i: ℕ) (p: P[X]) : p = p.erase i + term i (p i) := by
  ext j;
  simp [apply_erase]
  split; rw [zero_add]; congr
  rw [add_zero]

private def with_degree (p: P[X]) (deg: ℕ) (hdeg: ∀i, deg ≤ i -> p i = 0) : P[X] where
  toFun := p
  spec := Trunc.mk {
    degree_p1 := deg
    spec := hdeg
  }

private def eq_with_degree (p: P[X]) (deg: ℕ) (hdeg: ∀i, deg ≤ i -> p i = 0) : p = p.with_degree deg hdeg := by ext; rfl

@[simp] def apply_smul [SMul R P] [IsLawfulSMulZero R P] (i: ℕ) (r: R) (p: P[X]) : (r • p) i = r • p i := rfl

def smul_term [SMul R P] [IsLawfulSMulZero R P] (n: ℕ) (r: R) (p: P) : r • term n p = term n (r • p) := by
  ext j; simp
  split; rfl; rw [smul_zero]

instance [SemiringOps R] [IsSemiring R] [SMul R P] [IsModule R P] : IsModule R P[X] where
  zero_smul _ := by ext i; apply zero_smul
  smul_zero _ := by ext i; apply smul_zero
  one_smul _ := by ext i; apply one_smul
  mul_smul _ _ _ := by ext i; apply mul_smul
  smul_add _ _ _ := by ext i; apply smul_add
  add_smul _ _ _ := by ext i; apply add_smul

instance : IsModule P P[X] := inferInstance

private def list_induction'
  {motive: P[X] -> Prop}
  (zero: motive 0)
  (term_add: ∀(p: P) (n: ℕ) (ps: P[X]), motive ps -> motive (term n p + ps))
  (ps: P[X]) : motive ps := by
  obtain ⟨ps, hps⟩ := ps
  induction hps with | _ hps =>
  obtain ⟨deg, hps⟩ := hps
  induction deg generalizing ps with
  | zero =>
    have : ps = (fun _ => 0) := ?_
    subst ps
    apply zero
    ext i; apply hps
    apply Nat.zero_le
  | succ n ih =>
    let ps' : P[X] := {
      toFun := ps
      spec := Trunc.mk {
        degree_p1 := n + 1
        spec := hps
      }
    }
    show motive ps'
    rw [ps'.erase_add_term n, add_comm]
    apply term_add
    rw [eq_with_degree (erase _ _) n]
    apply ih
    intro i hi
    simp [apply_erase]
    intro hi'
    apply hps
    apply Nat.succ_le_of_lt
    apply Nat.lt_of_le_of_ne
    assumption
    exact Ne.symm hi'

@[induction_eliminator]
private def induction
  {motive: P[X] -> Prop}
  (term: ∀(p: P) (n: ℕ), motive (term n p))
  (add: ∀(a b: P[X]), motive a -> motive b -> motive (a + b))
  (ps: P[X]) : motive ps := by
  induction ps using list_induction' with
  | zero =>
    rw [←map_zero (Poly.term 0)]
    apply term
  | term_add =>
    apply add
    apply term
    assumption

section

variable [AddMonoidOps S] [IsAddMonoid S] [IsAddComm S]

private def preLiftAdd' (f: ℕ -> P →+ S) (p: P[X]) : S :=
  p.spec.lift (fun ha => ∑i: Fin ha.degree_p1, f i.val (p i.val)) <| by
    show ∀a b: DegreeRepr p, _
    intro a b; dsimp
    rw [fin_sum_min' (n := a.degree_p1) (m := a.degree_p1 ⊓ b.degree_p1)]
    rw [fin_sum_min' (n := b.degree_p1) (m := a.degree_p1 ⊓ b.degree_p1)]
    rfl
    any_goals apply min_le_right
    any_goals apply min_le_left
    all_goals
      intro i hi
      rcases min_eq a.degree_p1 b.degree_p1 with h | h
      rw [h] at hi
      rw [a.spec, map_zero]
      assumption
      rw [h] at hi
      rw [b.spec, map_zero]
      assumption

private def preLiftAdd (f: ℕ -> P →+ S) : P[X] →+ S where
  toFun := preLiftAdd' f
  map_zero := rfl
  map_add a b := by
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    induction ha with | mk ha =>
    induction hb with | mk hb =>
    show preLiftAdd' f (Poly.mk _ _) = _
    dsimp [preLiftAdd']
    simp [map_add]
    rw [sum_pairwise]
    congr 1
    rw [fin_sum_min']; rfl
    apply left_le_max
    intro i hi
    rw [ha.spec, map_zero]
    assumption
    rw [fin_sum_min']; rfl
    apply right_le_max
    intro i hi
    rw [hb.spec, map_zero]
    assumption

private def preLiftAdd_term (f: ℕ -> P →+ S) (n: ℕ) (p: P) : preLiftAdd f (term n p) = f n p := by
  simp only [preLiftAdd, term, AddGroupHom.apply_mk, preLiftAdd', apply_mk, Trunc.lift_mk]
  rw [fin_sum_succ_last, sum_zero', zero_add]
  simp
  intro i; rw [if_neg, map_zero]
  apply Nat.ne_of_lt i.isLt

def liftAdd : (ℕ -> P →+ S) ≃ (P[X] →+ S) where
  toFun f := preLiftAdd f
  invFun f n := {
    toFun p := f (term n p)
    map_zero := by rw [map_zero ,map_zero]
    map_add a b := by rw [map_add, map_add]
  }
  leftInv f := by
    ext p; simp
    induction p with
    | add => rw [map_add, map_add]; congr
    | term p n => rw [preLiftAdd_term]; rfl
  rightInv f := by
    ext n p; simp
    rw [preLiftAdd_term]

def liftAdd_term (f: ℕ -> P →+ S) (n: ℕ) (p: P) : liftAdd f (term n p) = f n p := preLiftAdd_term _ _ _

def map_liftAdd_add_func (f g: ℕ -> P →+ S) (p: P[X]) :
  liftAdd (fun n => f n + g n) p = liftAdd f p + liftAdd g p := by
  induction p with
  | add a b iha ihb =>
    rw [map_add, map_add, map_add, iha, ihb]
    ac_rfl
  | term =>
    simp [liftAdd_term]
    rfl

end

def mulHom : P[X] →+ P[X] →+ P[X] :=
  liftAdd <| fun n => {
    toFun a := liftAdd <| fun m => {
      toFun b := term (n + m) (a * b)
      map_zero := by rw [mul_zero, map_zero]
      map_add b₀ b₁ := by rw [mul_add, map_add]
    }
    map_zero := by
      apply DFunLike.ext; intro b
      simp [zero_mul, map_zero]
      show liftAdd (fun _ => 0) b = _
      induction b with
      | add _ _ iha ihb => rw [map_add, map_add, iha, ihb]
      | term =>
        rw [liftAdd_term]
        rfl
    map_add a₀ a₁ := by
      apply DFunLike.ext; intro p
      simp [add_mul, map_add]
      let (x: P) (m: ℕ) : P →+ P[X] := {
        toFun b := term (n + m) (x * b)
        map_zero := by rw [mul_zero, map_zero]
        map_add b₀ b₁ := by rw [mul_add, map_add]
      }
      show liftAdd (fun m => this a₀ m + this a₁ m) _ = _
      rw [map_liftAdd_add_func]
      rfl
  }

instance : Mul P[X] where
  mul a b := mulHom a b

instance : IsLawfulZeroMul P[X] where
  zero_mul a := by
    show mulHom 0 a = 0
    rw [map_zero]; rfl
  mul_zero a := by
    show mulHom a 0 = 0
    rw [map_zero]

instance : IsLeftDistrib P[X] where
  mul_add k a b := by
    show mulHom k (a + b) = _
    rw [map_add]; rfl

instance : IsRightDistrib P[X] where
  add_mul a b k := by
    show mulHom (a + b) k = _
    rw [map_add]; rfl

private def preC : P →+ P[X] := term 0

instance : One P[X] where
  one := preC 1

def coeff (k: ℕ) : P[X] →+ P where
  toFun p := p k
  map_zero := rfl
  map_add _ _ := rfl

@[simp] def apply_coeff (p: P[X]) (k: ℕ) : coeff k p = p k := rfl

def term_mul_term (n m: ℕ) (a b: P) : term n a * term m b = term (n + m) (a * b) := by
  show mulHom _ _ = _
  unfold mulHom
  simp [liftAdd_term]

def C : P ↪+* P[X] where
  toAddGroupHom := preC
  map_one := rfl
  map_mul := by
    intro a b
    show preC (_ * _) = preC _ * preC _
    show term _ _ = term _ a * term _ b
    rw [term_mul_term]
  inj := by
    intro a b h
    replace h : preC a = preC b := h
    show preC a 0 = preC b 0
    rw [h]

instance : NatCast P[X] where
  natCast n := C n

def natCast_eq_C (n: ℕ) : (n: P[X]) = C (n: P) := rfl

instance : Pow P[X] ℕ := defaultPowN

instance : IsLawfulPowN P[X] where

def term_pow (n d: ℕ) (p: P) : (term d p) ^ n = term (d * n) (p ^ n) := by
  induction n generalizing d p with
  | zero => rw [npow_zero, mul_zero, npow_zero]; rfl
  | succ n ih => rw [npow_succ, npow_succ, Nat.mul_succ, ih, term_mul_term]

def term_def (n: ℕ) (p: P) : term n p = p • ((X: P[X]) ^ n) := by
  show term _ _ = p • term _ _ ^ _
  rw [term_pow, one_npow, one_mul, smul_term]
  show _ = term _ (p * 1)
  rw [mul_one]

def C_mul_eq_smul (p: P) (ps: P[X]) : C p * ps = p • ps := by
  induction ps with
  | add a b iha ihb => rw [smul_add, mul_add, iha, ihb]
  | term p' n =>
    rw [smul_term]
    show term _ _ * _ = _
    rw [term_mul_term, zero_add]; rfl

def mul_C_eq_smul [IsComm P] (p: P) (ps: P[X]) : ps * C p = p • ps := by
  induction ps with
  | add a b iha ihb => rw [smul_add, add_mul, iha, ihb]
  | term p' n =>
    rw [smul_term]
    show _  * term _ _ = _
    rw [term_mul_term, add_zero, mul_comm]; rfl

instance : SemiringOps P[X] := inferInstance

instance : IsLawfulNatCast P[X] where
  natCast_zero := by rw [natCast_eq_C, natCast_zero, map_zero]
  natCast_one := by rw [natCast_eq_C, natCast_one, map_one]
  natCast_succ n := by rw [natCast_eq_C, natCast_eq_C, natCast_succ, map_add, map_one]

instance : IsSemigroup P[X] where
  mul_assoc a b c := by
    induction a with
    | add a₀ a₁ ih₀ ih₁ =>
      iterate 3 rw [add_mul]
      rw [ih₀, ih₁]
    | term p₀ n₀ =>
    induction b with
    | add b₀ b₁ ih₀ ih₁ =>
      simp [mul_add, add_mul]
      rw [ih₀, ih₁]
    | term p₁ n₁ =>
    induction c with
    | add b₀ b₁ ih₀ ih₁ =>
      simp [mul_add]
      rw [ih₀, ih₁]
    | term p₂ n₂ =>
      simp [term_mul_term]
      rw [add_assoc, mul_assoc]

instance [IsComm P] : IsLawfulOneMul P[X] where
  one_mul a := by
    induction a with
    | add a b iha ihb => simp [mul_add, iha, ihb]
    | term p n => rw [←map_one C, C_mul_eq_smul, one_smul]
  mul_one a := by
    induction a with
    | add a b iha ihb => simp [add_mul, iha, ihb]
    | term p n => rw [←map_one C, mul_C_eq_smul, one_smul]

instance [IsComm P] : IsSemiring P[X] where
instance [IsComm P] : IsComm P[X] where
  mul_comm a b := by
    induction a generalizing b with
    | add a₀ a₁ ih₀ ih₁ => rw [mul_add, add_mul, ih₀, ih₁]
    | term p₀ n₀ =>
    induction b with
    | add a₀ a₁ ih₀ ih₁ => rw [mul_add, add_mul, ih₀, ih₁]
    | term p₁ n₁ => rw [term_mul_term, term_mul_term, mul_comm, add_comm]

instance [IsComm P] [HasChar P n] : HasChar P[X] n :=
  HasChar.of_ring_emb (α := P) (β := P[X]) C

instance : AlgebraMap P P[X] where
  toAlgebraMap := C.toRingHom
instance [IsComm P] : IsAlgebra P P[X] where
  smul_def _ _ := (C_mul_eq_smul _ _).symm
  commutes p ps := by
    show C p * ps = ps * C p
    rw [mul_comm]

variable [SemiringOps S] [IsSemiring S] [IsComm S]
  [SMul P S] [AlgebraMap P S] [IsAlgebra P S]

private def preEval (x: S) : P[X] →+ S :=
  liftAdd (fun n => {
    toFun p := p • x ^ n
    map_zero := by rw [zero_smul]
    map_add a b := by rw [add_smul]
  })

def eval
  (P: Type*) [SemiringOps P] [IsSemiring P]
  [SMul P S] [AlgebraMap P S] [IsAlgebra P S]
  (x: S) : P[X] →ₐ[P] S where
  toAddGroupHom := preEval x
  map_one := by
    show liftAdd _ (term _ _) = _
    rw [liftAdd_term]; simp
    rw [npow_zero, one_smul]
  map_mul a b := by
    show liftAdd _ _ = liftAdd _ a * liftAdd _ b
    induction a with
    | add a b iha ihb => simp [add_mul, map_add, iha, ihb]
    | term =>
    induction b with
    | add a b iha ihb => simp [mul_add, map_add, iha, ihb]
    | term =>
      simp [liftAdd_term, term_mul_term, smul_def]
      rw [npow_add, map_mul]
      ac_rfl
  map_smul r p := by
    show preEval _ (r • p) = r • preEval _ p
    induction p with
    | add a b iha ihb => rw [smul_add, map_add, iha, ihb,
      map_add, smul_add]
    | term p n =>
      show liftAdd _ _ = r • liftAdd _ _
      rw [smul_term, liftAdd_term, liftAdd_term]
      dsimp
      rw [smul_assoc]

def eval_term (x: S) (n: ℕ) (p: P) : eval P x (term n p) = p • x ^ n := by
  apply liftAdd_term

def eval_X (x: S) : eval P x (X: P[X]) = x := by
  simp [Poly.X]
  rw [eval_term, npow_one, one_smul]

def eval_C (x: S) (p: P) : eval P x (C p) = algebraMap P p := by
  show eval P x (term 0 p) = algebraMap P p
  rw [eval_term, npow_zero, smul_def, mul_one]

variable [SemiringOps R] [IsSemiring R] [IsComm R]

private def cast_val (f: P →+* R) : IsAlgebra.OfRingHom (C.toRingHom.comp f) (by intro _ _; rw [mul_comm]) :=
  Poly.X

def cast (f: P →+* R) : P[X] →+* R[X] :=
  (eval P (cast_val f)).toRingHom

def cast_term {f: P →+* R} (n: ℕ) (p: P) : cast f (term n p) = term n (f p) := by
  unfold cast
  show eval P (cast_val f) (term n p) = _
  rw [eval_term, term_def, smul_def, smul_def]
  rfl

def cast_X {f: P →+* R} : cast f Poly.X = Poly.X := by
  simp [Poly.X]
  rw [cast_term, map_one]

def cast_C {f: P →+* R} (p: P) : cast f (C p) = C (f p) := by
  show cast f (term _ _) = term _ _
  rw [cast_term]

end Poly
