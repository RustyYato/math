import LeanMath.Data.DirectSum.Defs

structure LinearCombo (R α: Type*) [Zero R] [Add R] where
  ofDirectSum :: toDirectSum : ⊕_: α, R

namespace LinearCombo

instance [Zero R] [Add R] : Zero (LinearCombo R α) where
  zero := ⟨0⟩

instance [Zero R] [Add R] : Add (LinearCombo R α) where
  add a b := ⟨a.toDirectSum + b.toDirectSum⟩

def equivDirectSum [Zero R] [Add R] : LinearCombo R α ≃+ ⊕_: α, R where
  toFun a := a.toDirectSum
  invFun := ofDirectSum
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_add _ _ := rfl

instance [SMul S R] [MonoidOps S] [IsMonoid S]
  [AddMonoidOps R] [IsAddMonoid R] [IsDistributiveAction S R]
  : SMul S (LinearCombo R α) where
  smul s a := ⟨s • a.toDirectSum⟩

variable [AddMonoidOps R] [IsAddMonoid R] [IsAddComm R]

def ι (a: α) : R →+ LinearCombo R α :=
  equivDirectSum.symm.toAddGroupHom.comp (DirectSum.ι (R := fun _ => R) a)

def smul_ι [SMul S R] [MonoidOps S] [IsMonoid S] [IsDistributiveAction S R] (a: α) (r: R) (s: S) :
  s • ι a r = ι a (s • r) := by
  simp [ι, ←DirectSum.smul_ι]
  rfl

@[simp] def equivDirectSum_ι (a: α) (r: R) : equivDirectSum (ι a r) = DirectSum.ι a r := rfl
@[simp] def symm_equivDirectSum_ι (a: α) (r: R) : equivDirectSum.symm (.ι a r) = ι a r := rfl

def ιHom (S: Type*) [SMul S R] [MonoidOps S] [IsMonoid S] [IsDistributiveAction S R] (a: α) : R →ₗ[S] LinearCombo R α where
  toAddHom := (ι a).toAddHom
  map_smul _ _ := by symm; apply smul_ι

variable {S: Type*} [SMul S R] [MonoidOps S] [IsMonoid S] [IsDistributiveAction S R]

@[simp] def ιHom_eq_ι (a: α) (r: R) : ιHom S a r = ι a r := rfl

instance : IsLawfulSMulZero S (LinearCombo R α) where
  smul_zero s := by
    show equivDirectSum.symm (s • 0) = 0
    rw [smul_zero, map_zero]

instance : IsRightDistribSMul S (LinearCombo R α) where
  smul_add s a b := by
    show equivDirectSum.symm (s • (equivDirectSum a + equivDirectSum b)) = _
    rw [smul_add]; rfl

def list_induction
  {motive: LinearCombo R α -> Prop}
  (zero: motive 0)
  (ι_add: ∀(a: α) (r: R) (b: LinearCombo R α), motive b -> motive (ι a r + b))
  (a: LinearCombo R α) : motive a := by
  obtain ⟨a⟩ := a
  induction a using DirectSum.list_induction with
  | zero => apply zero
  | ι_add =>
    apply ι_add
    assumption

@[induction_eliminator]
def induction
  {motive: LinearCombo R α -> Prop}
  (zero: motive 0)
  (ι: ∀(a: α) (r: R), motive (ι a r))
  (add: ∀(a b: LinearCombo R α), motive a -> motive b -> motive (a + b))
  (a: LinearCombo R α) : motive a := by
  induction a using list_induction with
  | zero => apply zero
  | ι_add =>
    apply add
    apply ι
    assumption

instance : SMul ℕ (LinearCombo R α) := inferInstance

instance : IsAddComm (LinearCombo R α) where
  add_comm a b := by
    show equivDirectSum.symm (equivDirectSum a + equivDirectSum b) = _
    rw [add_comm]; rfl

instance : IsLawfulZeroAdd (LinearCombo R α) where
  zero_add a := by
    show equivDirectSum.symm (0 + equivDirectSum a) = _
    rw [zero_add]; rfl
  add_zero a := by
    show equivDirectSum.symm (equivDirectSum a + 0) = _
    rw [add_zero]; rfl

instance : IsAddSemigroup (LinearCombo R α) where
  add_assoc a b c := by
    show equivDirectSum.symm (equivDirectSum a + equivDirectSum b + equivDirectSum c) = _
    rw [add_assoc]; rfl

instance : IsAddMonoid (LinearCombo R α) where
  zero_nsmul a := by
    show equivDirectSum.symm (_ • equivDirectSum a) = _
    rw [zero_nsmul]; rfl
  succ_nsmul n a := by
    show equivDirectSum.symm (_ • equivDirectSum a) = _
    rw [succ_nsmul]; rfl

instance : IsDistributiveAction S (LinearCombo R α) where
  one_smul a := by
    show equivDirectSum.symm (_ • equivDirectSum a) = _
    rw [one_smul]; rfl
  mul_smul r s a := by
    show equivDirectSum.symm (_ • equivDirectSum a) = _
    rw [mul_smul]; rfl

variable [AddMonoidOps M] [IsAddMonoid M] [IsAddComm M]

def lift : (α -> R →+ M) ≃ (LinearCombo R α) →+ M where
  toFun f := (DirectSum.lift f).comp equivDirectSum.toAddGroupHom
  invFun f := fun a => f.comp (ι a)
  leftInv f := by
    apply DFunLike.ext; intro x; simp
    induction x with
    | zero => simp [map_zero]
    | add a b iha ihb => simp [map_add, iha, ihb]
    | ι a r => simp
  rightInv f := by ext a r; simp

@[simp] def lift_ι (f: α -> R →+ M) (a: α) (r: R) : lift f (ι a r) = f a r := by
  show (DirectSum.lift f) (equivDirectSum (ι a r)) = _
  simp

attribute [irreducible] ι lift

instance [Subsingleton R] : Subsingleton (LinearCombo R α) where
  allEq := by
    suffices ∀a: LinearCombo R α, a = 0 by
      intro a b
      rw [this a, this b]
    intro a
    induction a with
    | zero => rfl
    | ι a r => rw [Subsingleton.allEq r 0, map_zero]
    | add a b iha ihb =>
      rw [iha, ihb, add_zero]

def get [DecidableEq α] (a: α) : (LinearCombo R α) →+ R :=
  lift (fun b => if a = b then AddGroupHom.id _ else 0)

def get_ι [DecidableEq α] (a b: α) (r: R) : get a (ι b r) = if a = b then r else 0 := by
  unfold get; rw [lift_ι]
  split <;> rfl

end LinearCombo
