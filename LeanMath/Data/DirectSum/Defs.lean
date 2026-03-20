import LeanMath.Algebra.Monoid.Free
import LeanMath.Algebra.Monoid.Action.Defs

section

variable {α: Type*} (R: α -> Type*)

open FreeMonoid in
inductive DirectSum.Rel [∀a, Zero (R a)] [∀a, Add (R a)] : FreeMonoid (Σa, R a) -> FreeMonoid (Σa, R a) -> Prop where
-- addition on a direct sum is compatible with the underlying scalars
| ι_mul_ι (a: α) (r₀ r₁: R a) : Rel (ι ⟨a, r₀⟩ * ι ⟨a, r₁⟩) (ι ⟨a, r₀ + r₁⟩)
-- addition on a direct sum commutes
| comm (a b: FreeMonoid (Σa, R a)) : Rel (a * b) (b * a)
-- zero of the direct sum is compaible with the underlying scalars
| ι_zero_eq_one (a: α): Rel (ι ⟨a, 0⟩) 1

def DirectSum.Con [∀a, Zero (R a)] [∀a, Add (R a)] : MulCon (FreeMonoid (Σa, R a)) :=
  MulCon.generate (DirectSum.Rel R)

structure DirectSum [∀a, Zero (R a)] [∀a, Add (R a)] where
  ofQuot :: toQuot : AlgQuot (DirectSum.Con R)

unsafe instance [∀a, Zero (R a)] [∀a, Add (R a)] [Repr α] [∀a, Repr (R a)] : Repr (DirectSum R) where
  reprPrec a := reprPrec (a.toQuot.lift id lcProof)

section Syntax

open Lean
open TSyntax.Compat

macro "⊕ " xs:explicitBinders ", " b:term:60 : term => expandExplicitBinders ``DirectSum xs b

@[app_unexpander DirectSum] def unexpand_DirectSum : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => ⊕ $xs:binderIdent*, $b) => `(⊕ $x:ident $xs:binderIdent*, $b)
  | `($(_) fun $x:ident => $b)                     => `(⊕ $x:ident, $b)
  | `($(_) fun ($x:ident : $t) => $b)              => `(⊕ ($x:ident : $t), $b)
  | _                                              => throw ()

end Syntax

end

namespace DirectSum

variable {α: Type*} {R: α -> Type*}

instance [∀a, Zero (R a)] [∀a, Add (R a)] : Zero (⊕a, R a) where
  zero := { toQuot := 1 }

instance [∀a, Zero (R a)] [∀a, Add (R a)] : Add (⊕a, R a) where
  add a b := { toQuot := a.toQuot * b.toQuot }

private def preι [∀a, Zero (R a)] [∀a, Add (R a)] (a: α) (r: R a) : ⊕a, R a where
  toQuot := AlgQuot.mk (DirectSum.Con _) (FreeMonoid.ι ⟨a, r⟩)

def ι [∀a, Zero (R a)] [∀a, Add (R a)] (a: α) : R a →+ ⊕a, R a where
  toFun := preι a
  map_zero := by
    simp [preι]
    show ofQuot _ = ofQuot _
    congr 1; apply AlgQuot.sound
    apply MulCon.generate_of
    apply Rel.ι_zero_eq_one
  map_add x y := by
    simp [preι]
    symm; show ofQuot _ = ofQuot _
    congr 1; apply AlgQuot.sound
    apply MulCon.generate_of
    apply Rel.ι_mul_ι

private def ι_toQuot [∀a, Zero (R a)] [∀a, Add (R a)] (a: α) (r: R a) : (ι a r).toQuot = AlgQuot.mk (DirectSum.Con _) (FreeMonoid.ι ⟨a, r⟩) := rfl

instance [∀a, Zero (R a)] [∀a, Add (R a)] : IsAddComm (⊕a, R a) where
  add_comm a b := by
    cases a with | ofQuot a =>
    cases b with | ofQuot b =>
    show ofQuot _ = ofQuot _
    congr 1
    induction a with | mk a =>
    induction b with | mk b =>
    apply AlgQuot.sound
    apply MulCon.generate_of
    apply Rel.comm

def list_induction
  [∀a, Zero (R a)] [∀a, Add (R a)]
  {motive: (⊕a, R a) -> Prop}
  (zero: motive 0)
  (ι_add: ∀(a: α) (r: R a) (b: ⊕a, R a), motive b -> motive (ι a r + b))
  (a: ⊕a, R a) : motive a := by
  cases a with | ofQuot a =>
  induction a with | _ a =>
  induction a using FreeMonoid.ι_induction with
  | one => apply zero
  | ι_mul x b ih =>
    rw [map_mul]
    apply ι_add
    assumption

@[induction_eliminator]
def induction
  [∀a, Zero (R a)] [∀a, Add (R a)]
  {motive: (⊕a, R a) -> Prop}
  (zero: motive 0)
  (ι: ∀(a: α) (r: R a), motive (ι a r))
  (add: ∀(a b: ⊕a, R a), motive a -> motive b -> motive (a + b))
  (a: ⊕a, R a) : motive a := by
  induction a using list_induction with
  | zero => apply zero
  | ι_add =>
    apply add
    apply ι
    assumption

section

variable
  {S: Type*} [MonoidOps S] [IsMonoid S] [∀a, SMul S (R a)]
  [∀a, AddMonoidOps (R a)] [∀a, IsAddMonoid (R a)] [∀a, IsDistributiveAction S (R a)]

private def smul₀ (s: S) : FreeMonoid (Σa, R a) →* FreeMonoid (Σa, R a) :=
  FreeMonoid.lift (fun x => FreeMonoid.ι ⟨x.1, s • x.2⟩)

private def smul₀_ι (s: S) (x: Σa, R a) : smul₀ s (FreeMonoid.ι x) = FreeMonoid.ι ⟨x.1, s • x.2⟩ :=
  FreeMonoid.lift_ι _ _

private def smul₁ (s: S) : AlgQuot (Con R) →* AlgQuot (Con R) :=
  AlgQuot.mapGroupHom (smul₀ s) (by
      unfold Con
      intro x y h
      refine MulCon.map _ ?_ h
      intro a b h
      apply MulCon.generate_of
      cases h with
      | ι_mul_ι =>
        simp [smul₀_ι, smul_add, map_mul]
        apply Rel.ι_mul_ι
      | comm =>
        rw [map_mul, map_mul]
        apply Rel.comm
      | ι_zero_eq_one =>
        simp [smul₀_ι, smul_zero, map_one]
        apply Rel.ι_zero_eq_one)

instance : SMul S (⊕i, R i) where
  smul s a := { toQuot := smul₁ s a.toQuot }

instance [∀a, Zero (R a)] [∀a, Add (R a)] [∀a, IsAddSemigroup (R a)]
  : IsAddSemigroup (⊕i, R i) where
  add_assoc := by
    intro a b c
    cases a with | _ a =>
    cases b with | _ b =>
    cases c with | _ c =>
    show ofQuot _ = ofQuot _
    congr 1
    apply mul_assoc

instance [∀a, Zero (R a)] [∀a, Add (R a)] [∀a, IsLawfulZeroAdd (R a)]
  : IsLawfulZeroAdd (⊕i, R i) where
  zero_add a := by
    cases a with | _ a =>
    show ofQuot (1 * _) = ofQuot _
    rw [one_mul]
  add_zero a := by
    cases a with | _ a =>
    show ofQuot (_ * 1) = ofQuot _
    rw [mul_one]

def smulAddHom (s: S) : (⊕a, R a) →+ (⊕a, R a) where
  toFun := (s • ·)
  map_zero := by
    show ofQuot (smul₁ s 1) = ofQuot _
    rw [map_one]
  map_add a b := by
    show ofQuot (smul₁ s (a.toQuot * b.toQuot)) = ofQuot _
    rw [map_mul]
    rfl

def smul_ι (s: S) (a: α) (r: R a) : s • ι a r = ι a (s • r) := by
  show ofQuot (smul₁ s (ι a r).toQuot) = _
  simp [smul₁, show (ι a r).toQuot = AlgQuot.mk (DirectSum.Con _) (FreeMonoid.ι ⟨a, r⟩) from rfl]
  congr 1; simp [smul₀]

variable [∀a, IsAddComm (R a)]

instance : IsAddMonoid (⊕i, R i) where
  zero_nsmul a := by
    show smulAddHom 0 a = 0
    induction a with
    | zero => rw [map_zero]
    | add a b iha ihb => rw [map_add, iha, ihb, add_zero]
    | ι a r =>
      show 0 • ι _ _ = _
      rw [smul_ι, zero_smul, map_zero]
  succ_nsmul n a := by
    show smulAddHom (n + 1) a = smulAddHom n a + a
    induction a with
    | zero => rw [map_zero, map_zero, add_zero]
    | add a b iha ihb =>
      rw [map_add, map_add, iha, ihb]; ac_rfl
    | ι a r =>
      show (n + 1) • ι _ _ = n • _ + _
      rw [smul_ι, succ_nsmul, map_add, ←smul_ι]

instance : IsLawfulSMulZero S (⊕i, R i) where
  smul_zero s := by apply map_zero (smulAddHom _)

instance : IsRightDistribSMul S (⊕i, R i) where
  smul_add := by
    intro s a b
    apply map_add (smulAddHom _)

instance : IsDistributiveAction S (⊕i, R i) where
  one_smul a := by
    induction a with
    | zero => rw [smul_zero]
    | add => rw [smul_add]; congr
    | ι a r => rw [smul_ι, one_smul]
  mul_smul r s a := by
    induction a with
    | zero => simp [smul_zero]
    | add => simp[smul_add]; congr
    | ι a r => simp [smul_ι, mul_smul]

variable [AddMonoidOps M] [IsAddMonoid M] [IsAddComm M]

private def preLift₀ (f: ∀a, R a →+ M) : AlgQuot (DirectSum.Con R) →* MulOfAdd M :=
  AlgQuot.liftGroupHom {
    val := (FreeMonoid.lift (fun x => MulOfAdd.mk (f x.1 x.2)))
    property := by
      intro x y h
      apply MulCon.map (S := EqCon _) _ _ h
      exact default
      intro a b r
      show _ = _
      cases r with
      | comm => rw [map_mul, map_mul, mul_comm]
      | ι_mul_ι =>
        simp [map_mul, FreeMonoid.lift_ι, map_add]
        rfl
      | ι_zero_eq_one =>
        simp
        rw [map_zero, map_one]
        rfl
  }

private def preLift (f: ∀a, R a →+ M) : (⊕a, R a) →+ M where
  toFun x := (preLift₀ f x.toQuot).get
  map_zero := by
    show (preLift₀ f 1).get = 0
    rw [map_one]; rfl
  map_add a b := by
    show (preLift₀ f (a.toQuot * b.toQuot)).get = _
    rw [map_mul]; rfl

private def preLift_ι (f: ∀a, R a →+ M) (a: α) (r: R a) : preLift f (ι a r) = f a r := by
  show (preLift₀ f (AlgQuot.mk (Con _) _)).get = f a r
  unfold preLift₀
  simp
  rfl

def lift : (∀a, R a →+ M) ≃ (⊕a, R a) →+ M where
  toFun := preLift
  invFun f := fun a => f.comp (ι a)
  leftInv f := by
    apply DFunLike.ext; intro x
    dsimp
    induction x with
    | zero => rw [map_zero, map_zero]
    | add a b iha ihb => rw [map_add, map_add, iha, ihb]
    | ι a r =>
      rw [preLift_ι]
      rfl
  rightInv f := by ext a r; apply preLift_ι

@[simp] def lift_ι (f: ∀a, R a →+ M) (a: α) (r: R a) : lift f (ι a r) = f a r := preLift_ι _ _ _

attribute [irreducible] lift ι

def get [DecidableEq α] (a: α) : (⊕a, R a) →+ R a :=
  lift (fun b => if h:a = b then cast (h ▸ rfl) (AddGroupHom.id (R b)) else 0)

def get_ι_eq [DecidableEq α] (a: α) (r: R a) : get a (ι a r) = r := by
  unfold get; rw [lift_ι, dif_pos rfl]
  dsimp; rfl

def get_ι_ne [DecidableEq α] (a b: α) (h: a ≠ b) (r: R b) : get a (ι b r) = 0 := by
  unfold get; rw [lift_ι, dif_neg h]; rfl

def from_elements : List (Σa, R a) -> ⊕a, R a :=
  List.foldr (fun x acc => ι x.1 x.2 + acc) 0

@[simp] def from_elements_nil : from_elements (α := α) (R := R) [] = 0 := rfl
@[simp] def from_elements_cons (a: (Σa, R a)) (as: List ((Σa, R a))) : from_elements (a::as) = ι a.1 a.2 + from_elements as := rfl

def from_elements_set_sum
  (elements: List (Σa, R a))
  (index: Nat) (hindex: index < elements.length)
  (a: α) (r₀ r₁: R a) :
  from_elements (elements.set index ⟨a, r₀ + r₁⟩) =
  from_elements (⟨a, r₀⟩::elements.set index ⟨a, r₁⟩) := by
  induction elements generalizing index with
  | nil => contradiction
  | cons x xs ih =>
    cases index with
    | zero => simp; rw [map_add, add_assoc]
    | succ index =>
      simp
      rw [ih]
      simp; ac_rfl
      apply Nat.lt_of_succ_lt_succ
      assumption

def from_elements_set_nodup
  (elements: List (Σa, R a))
  (index: Nat) (hindex: index < elements.length)
  (r: R elements[index].fst) :
  elements.Pairwise (fun x y => x.1 ≠ y.1) ->
  (elements.set index ⟨_, r⟩).Pairwise (fun x y => x.1 ≠ y.1) := by
  intro h
  rw [List.pairwise_iff_getElem] at h
  rw [List.pairwise_iff_getElem]
  intro i j hi hj i_lt_j
  simp [List.getElem_set]
  split; subst index
  rw [if_neg (Nat.ne_of_lt i_lt_j)]
  apply h; assumption
  split; subst index
  apply h; assumption
  apply h; assumption

private def exists_nodup_elements' [LEM] (lc: ⊕a, R a) : ∃elements: List (Σa, R a), elements.Pairwise (fun x y => x.1 ≠ y.1) ∧ lc = from_elements elements := by
  induction lc using list_induction with
  | zero => exact ⟨[], List.Pairwise.nil, rfl⟩
  | ι_add a r as ih =>
    obtain ⟨elements, nodup, eq⟩ := ih
    rcases em (∃index: Fin elements.length, elements[index].1 = a) with ha | ha
    · simp at ha
      obtain ⟨index, _⟩ := ha
      subst a
      refine ⟨elements.set index ⟨_, r + elements[index].snd⟩, ?_, ?_⟩
      · apply from_elements_set_nodup
        assumption
      · rw [from_elements_set_sum]
        simp; congr
        show as = from_elements (elements.set index elements[index.val])
        rw [List.set_getElem_self]
        assumption
        exact index.isLt
    · simp at ha
      refine ⟨⟨a, r⟩::elements, ?_, ?_⟩
      · apply List.Pairwise.cons
        intro x hx
        intro rfl
        rw [List.mem_iff_getElem] at hx
        obtain ⟨i, hi, h⟩ := hx
        have := ha ⟨i, hi⟩
        rw [←h] at this
        contradiction
        assumption
      · simp; congr

def exists_nodup_elements [LEM] (lc: ⊕a, R a) : ∃elements: List (Σa, R a), elements.Pairwise (fun x y => x.1 ≠ y.1) ∧ lc = from_elements elements ∧ ∀x ∈ elements, x.2 ≠ 0 := by
  have ⟨elements, nodup, eq⟩ := exists_nodup_elements' lc; subst lc
  suffices ∃e: List (Σa, R a), e.Sublist elements ∧ from_elements elements = from_elements e ∧ ∀x ∈ e, x.2 ≠ 0 by
    obtain ⟨e, sub, eq, h⟩ := this
    refine ⟨e, ?_, eq, h⟩
    apply List.pairwise_of_forall_sublist
    intro x y h
    replace h := List.Sublist.trans h sub
    apply List.pairwise_iff_forall_sublist.mp nodup
    assumption
  induction nodup with
  | nil => exact ⟨[], List.Sublist.slnil, rfl, nofun⟩
  | @cons a as head tail ih =>
    obtain ⟨bs, bssub, bseq, bsnezero⟩ := ih
    rcases em (a.2 = 0) with hr | hr
    · refine ⟨bs, ?_, ?_, ?_⟩
      · apply List.Sublist.cons
        assumption
      · rw [from_elements_cons, bseq, hr, map_zero, zero_add]
      · assumption
    · refine ⟨a::bs, ?_, ?_, ?_⟩
      · apply List.Sublist.cons₂
        assumption
      · rw [from_elements_cons, from_elements_cons, bseq]
      · intro x hx
        cases hx
        assumption
        apply bsnezero
        assumption

end

end DirectSum
