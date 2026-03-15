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

private def mul (a b: P[X]) (ha: DegreeRepr a.toFun) (hb: DegreeRepr b.toFun) : P[X] :=
  ∑(i: Fin ha.degree_p1) (j: Fin hb.degree_p1), term (i.val + j.val) (a i.val * b j.val)

private def mul_congr (a b: P[X])
  (ha₁: DegreeRepr a.toFun) (hb₁: DegreeRepr b.toFun)
  (ha₂: DegreeRepr a.toFun) (hb₂: DegreeRepr b.toFun):
  mul a b ha₁ hb₁ = mul a b ha₂ hb₂ := by
  dsimp [mul]
  obtain ⟨da₁, ha₁⟩ := ha₁
  obtain ⟨db₁, hb₁⟩ := hb₁
  obtain ⟨da₂, ha₂⟩ := ha₂
  obtain ⟨db₂, hb₂⟩ := hb₂
  dsimp at ha₁ hb₁ ha₂ hb₂
  rw [fin_sum_min' _ (n := da₁) (da₁ ⊓ da₂) _]
  rw [fin_sum_min' _ (n := da₂) (da₁ ⊓ da₂) _]
  rw [sum_comm, sum_comm (ι' := Fin db₂)]
  rw [fin_sum_min' _ (n := db₁) (db₁ ⊓ db₂) _]
  rw [fin_sum_min' _ (n := db₂) (db₁ ⊓ db₂) _]
  rfl
  any_goals
    intro i hi
    rcases min_eq da₁ da₂ with h | h
    rw [ha₁ i.val]; conv => { arg 1; arg 1; intro j; rw [zero_mul, map_zero] }
    rw [sum_zero]; apply le_trans _ hi; rw [h]
    rw [ha₂ i.val]; conv => { arg 1; arg 1; intro j; rw [zero_mul, map_zero] }
    rw [sum_zero]; apply le_trans _ hi; rw [h]
  any_goals
    intro i hi
    rcases min_eq db₁ db₂ with h | h
    rw [hb₁ i.val]; conv => { arg 1; arg 1; intro j; rw [mul_zero, map_zero] }
    rw [sum_zero]; apply le_trans _ hi; rw [h]
    rw [hb₂ i.val]; conv => { arg 1; arg 1; intro j; rw [mul_zero, map_zero] }
    rw [sum_zero]; apply le_trans _ hi; rw [h]
  any_goals apply min_le_left
  any_goals apply min_le_right

instance : Mul P[X] where
  mul a b :=
    a.spec.liftOn₂ b.spec (mul a b) <| by
    intro a₁ b₁ a₂ b₂ h g; clear h g
    apply mul_congr a b

private def mulHom : P[X] →+ P[X] →+ P[X] where
  toFun a := {
    toFun b := a * b
    map_zero := by
      obtain ⟨a, ha⟩ := a
      induction ha with | _ ha =>
      show mul ⟨a, _⟩  0 _ _ = _
      unfold mul
      simp [sum_zero]
    map_add b₀ b₁ := by
      obtain ⟨a, ha⟩ := a
      obtain ⟨b₀, hb₀⟩ := b₀
      obtain ⟨b₁, hb₁⟩ := b₁
      induction ha with | _ ha =>
      induction hb₀ with | _ hb₀ =>
      induction hb₁ with | _ hb₁ =>
      show mul ⟨a, _⟩ (⟨b₀, _⟩ + ⟨b₁, _⟩) _ _ =
        mul ⟨a, _⟩ ⟨b₀, _⟩ _ _ +
        mul ⟨a, _⟩ ⟨b₁, _⟩ _ _
      unfold mul
      simp [mul_add, map_add]
      rw [←sum_pairwise,]
      congr 1; funext i
      rw [sum_pairwise]
      congr 1
      rw [fin_sum_min']; rfl
      apply left_le_max
      intro j hj; rw [hb₀.spec, mul_zero, map_zero]
      assumption
      rw [fin_sum_min']; rfl
      apply right_le_max
      intro j hj; rw [hb₁.spec, mul_zero, map_zero]
      assumption
  }
  map_zero := by
    apply DFunLike.ext; intro b
    show 0 * b = 0
    obtain ⟨b, hb⟩ := b
    induction hb with | _ hb =>
    show mul 0 ⟨b, _⟩ _ _ = _
    simp [mul]
  map_add a₀ a₁ := by
    apply DFunLike.ext; intro b
    show (a₀ + a₁) * b = a₀ * b + a₁ * b
    obtain ⟨a₀, ha₀⟩ := a₀
    obtain ⟨a₁, ha₁⟩ := a₁
    obtain ⟨b, hb⟩ := b
    induction ha₀ with | _ ha₀ =>
    induction ha₁ with | _ ha₁ =>
    induction hb with | _ hb =>
    show mul (⟨a₀, _⟩ + ⟨a₁, _⟩)  ⟨b, _⟩ _ _ =
      mul ⟨a₀, _⟩ ⟨b, _⟩ _ _ +
      mul ⟨a₁, _⟩ ⟨b, _⟩ _ _
    simp [mul]
    simp [add_mul, map_add]
    iterate 3 rw [sum_comm _ (ι' := Fin hb.degree_p1)]
    rw [←sum_pairwise]
    congr 1; funext j
    rw [sum_pairwise]
    congr 1
    rw [fin_sum_min']; rfl
    apply left_le_max
    intro i hi ; rw [ha₀.spec, zero_mul, map_zero]
    assumption
    rw [fin_sum_min']; rfl
    apply right_le_max
    intro i hi ; rw [ha₁.spec, zero_mul, map_zero]
    assumption

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
  show mul (term n a) (term m b) _ _ = _
  simp only [mul, apply_term]
  ext k; show coeff k _  = _
  simp only [←map_sum]
  simp only [apply_coeff, apply_term]
  rw [
    fin_sum_succ_last,
    fin_sum_succ_last,
    sum_zero', sum_zero',
    zero_add, zero_add
  ]
  simp
  · intro i; simp; intro
    rw [if_neg, mul_zero]
    apply Nat.ne_of_lt i.isLt
  · intro i; rw [sum_zero']
    intro j; simp; intro
    rw [if_neg, zero_mul]
    apply Nat.ne_of_lt i.isLt

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

@[simp] def apply_smul [SMul R P] [IsLawfulSMulZero R P] (i: ℕ) (r: R) (p: P[X]) : (r • p) i = r • p i := rfl

def smul_term [SMul R P] [IsLawfulSMulZero R P] (n: ℕ) (r: R) (p: P) : r • term n p = term n (r • p) := by
  ext j; simp
  split; rfl; rw [smul_zero]

def term_def (n: ℕ) (p: P) : term n p = p • ((X: P[X]) ^ n) := by
  show term _ _ = p • term _ _ ^ _
  rw [term_pow, one_npow, one_mul, smul_term]
  show _ = term _ (p * 1)
  rw [mul_one]

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

def list_induction
  {motive: P[X] -> Prop}
  (zero: motive 0)
  (term_add: ∀(p: P) (n: ℕ) (ps: P[X]), motive ps -> motive (p • (X: P[X]) ^ n + ps))
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
    rw [ps'.erase_add_term n, add_comm, term_def]
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

instance : IsModule P P[X] where
  zero_smul _ := by ext i; apply zero_mul
  smul_zero _ := by ext i; apply mul_zero
  one_smul _ := by ext i; apply one_mul
  mul_smul _ _ _ := by ext i; apply mul_assoc
  smul_add _ _ _ := by ext i; apply mul_add
  add_smul _ _ _ := by ext i; apply add_smul

@[induction_eliminator]
def induction
  {motive: P[X] -> Prop}
  (term: ∀(p: P) (n: ℕ), motive (p • (X: P[X]) ^ n))
  (add: ∀(a b: P[X]), motive a -> motive b -> motive (a + b))
  (ps: P[X]) : motive ps := by
  induction ps using list_induction with
  | zero =>
    rw [←zero_smul (R := P) (α := P[X]) 1, ←npow_zero]
    apply term
  | term_add =>
    apply add
    apply term
    assumption

def C_mul_eq_smul (p: P) (ps: P[X]) : C p * ps = p • ps := by
  induction ps with
  | add a b iha ihb => rw [smul_add, mul_add, iha, ihb]
  | term p' n =>
    rw [←mul_smul, ←term_def, ←term_def]
    show term _ _ * _ = _
    rw [term_mul_term, zero_add]

def mul_C_eq_smul [IsComm P] (p: P) (ps: P[X]) : ps * C p = p • ps := by
  induction ps with
  | add a b iha ihb => rw [smul_add, add_mul, iha, ihb]
  | term p' n =>
    rw [←mul_smul, ←term_def, ←term_def]
    show _  * term _ _ = _
    rw [term_mul_term, add_zero, mul_comm]

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
      simp [←term_def, term_mul_term]
      rw [add_assoc, mul_assoc]

instance [IsComm P] : IsLawfulOneMul P[X] where
  one_mul a := by
    induction a with
    | add a b iha ihb => simp [mul_add, iha, ihb]
    | term p n =>
      rw [←term_def, ←map_one C, C_mul_eq_smul, one_smul]
  mul_one a := by
    induction a with
    | add a b iha ihb => simp [add_mul, iha, ihb]
    | term p n =>
      rw [←term_def, ←map_one C, mul_C_eq_smul, one_smul]

instance [IsComm P] : IsSemiring P[X] where
instance [IsComm P] : IsComm P[X] where
  mul_comm a b := by
    induction a generalizing b with
    | add a₀ a₁ ih₀ ih₁ => rw [mul_add, add_mul, ih₀, ih₁]
    | term p₀ n₀ =>
    induction b with
    | add a₀ a₁ ih₀ ih₁ => rw [mul_add, add_mul, ih₀, ih₁]
    | term p₁ n₁ => rw [←term_def, ←term_def, term_mul_term, term_mul_term, mul_comm, add_comm]

instance [IsComm P] [HasChar P n] : HasChar P[X] n :=
  HasChar.of_ring_emb (α := P) (β := P[X]) C

instance : AlgebraMap P P[X] where
  toAlgebraMap := C.toRingHom
instance [IsComm P] : IsAlgebra P P[X] where
  smul_def _ _ := (C_mul_eq_smul _ _).symm
  commutes p ps := by
    show C p * ps = ps * C p
    rw [mul_comm]

end Poly
