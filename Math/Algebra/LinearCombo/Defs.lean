module

public import Math.Algebra.DirectSum.Defs
public import Math.Algebra.Module.Defs
public import Math.Algebra.Module.Hom.Defs
import Math.Data.List.Defs

namespace Math

public structure LinearCombo (ι α: Type*) [Zero α] [Add α] where
  ofDirectSum :: toDirectSum : ⊕_: ι, α

namespace LinearCombo

public instance [Zero α] [Add α] : Zero (LinearCombo ι α) where
  zero := ⟨0⟩
public instance [Zero α] [Add α] : Add (LinearCombo ι α) where
  add a b := ⟨a.toDirectSum + b.toDirectSum⟩
public instance [Zero α] [Add α] [SMul S α]
  [IsLawfulSMulZero S α]
  [IsRightDistribSMul S α]
  : SMul S (LinearCombo ι α) where
  smul s a := ⟨s • a.toDirectSum⟩

@[expose] public def addEqv [Zero α] [Add α] : (⊕_: ι, α) ≃+ LinearCombo ι α where
  toFun := ofDirectSum
  invFun := toDirectSum
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_add _ _ := rfl

@[expose] public def eqv (S: Type*) [Zero α] [Add α] [SMul S α]
  [IsLawfulSMulZero S α]
  [IsRightDistribSMul S α] : (⊕_: ι, α) ≃ₗ[S] LinearCombo ι α where
  toFun := ofDirectSum
  invFun := toDirectSum
  leftInv _ := rfl
  rightInv _ := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl

public instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsAddMonoid (LinearCombo ι α) :=
  OfEquiv.instIsAddMonoid addEqv.toEquiv
public instance [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α] : IsAddComm (LinearCombo ι α) :=
  OfEquiv.instIsAddComm addEqv.toEquiv

public instance
  [SemiringOps S] [IsSemiring S] [SMul S α]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  [IsModule S α] : IsModule S (LinearCombo ι α) :=
  OfEquiv.instIsModule addEqv.toEquiv

@[expose]
public protected def ι (S: Type*) [Zero α] [Add α] [SMul S α]
  [IsLawfulSMulZero S α]
  [IsRightDistribSMul S α] (i: ι) : α →ₗ[S] LinearCombo ι α where
  toFun a := ⟨DirectSum.ι i a⟩
  map_add _ _ := by rw [map_add]; rfl
  map_smul s a := by rw [←DirectSum.smul_ι]; rfl

public theorem inductionIn
  (S: Type*)
  [SemiringOps S] [IsSemiring S]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul S α] [IsModule S α]
  {motive: LinearCombo I α -> Prop}
  (zero: motive 0)
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (ι: ∀i a, motive (.ι S i a))
  (lc: LinearCombo I α) : motive lc := by
  obtain ⟨lc⟩ := lc; induction lc with
  | zero => apply zero
  | add => apply add <;> assumption
  | ι => apply ι

@[induction_eliminator]
public theorem induction
  [SemiringOps α] [IsSemiring α]
  {motive: LinearCombo I α -> Prop}
  (zero: motive 0)
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (ι: ∀i a, motive (.ι α i a))
  (lc: LinearCombo I α) : motive lc :=
  inductionIn α zero add ι lc

variable {α M: Type*}
  [SemiringOps α] [IsSemiring α]
  [AddMonoidOps M] [IsAddMonoid M] [IsAddComm M]
  [SMul α M] [IsModule α M]

theorem eqv_symm_ι : (eqv α).symm (.ι α i a) = DirectSum.ι (R := fun _ => α) i a := rfl

def preLift (f: ι -> M) : LinearCombo ι α →ₗ[α] M where
  toAddHom :=
    let f := DirectSum.liftAdd (smulHom ∘ f)
    { f.comp addEqv.symm.toAddGroupHom with }
  map_smul k lc := by
    show DirectSum.liftAdd (smulHom ∘ f) ((eqv α).symm (k • lc)) = k • DirectSum.liftAdd (smulHom ∘ f) ((eqv α).symm lc)
    induction lc with
    | zero => simp [map_zero, smul_zero]
    | add a b iha ihb => simp [map_add, smul_add, iha, ihb]
    | ι i a =>
      rw [map_smul]; simp [eqv_symm_ι, DirectSum.liftAdd_ι, DirectSum.smul_ι]
      apply mul_smul

theorem apply_preLift (f: ι -> M) (lc: LinearCombo ι α) :
  preLift f lc = DirectSum.liftAdd (smulHom ∘ f) ((eqv α).symm lc) := by
  rfl

theorem preLift_ι (f: ι -> M) (i: ι) (a: α) : preLift f (.ι α i a) = a • f i := by
  rw [apply_preLift]
  show DirectSum.liftAdd _ (DirectSum.ι _ _) = _
  rw [DirectSum.liftAdd_ι]
  rfl

public def lift : (ι -> M) ≃ (LinearCombo ι α →ₗ[α] M) where
  toFun := preLift
  invFun f i := f (.ι α i 1)
  leftInv f := by
    ext lc; dsimp
    induction lc with
    | zero => simp [map_zero]
    | add a b iha ihb => simp [map_add, iha, ihb]
    | ι i a => simp [preLift_ι, ←map_smul, smul_eq_mul, mul_one]
  rightInv f := by ext i; dsimp; rw [preLift_ι, one_smul]

public theorem lift_ι (f: ι -> M) (i: ι) (a: α) : lift f (.ι α i a) = a • f i := preLift_ι _ _ _

public def get [DecidableEq ι] (i: ι) : LinearCombo ι α →ₗ[α] α :=
  lift fun j => if i = j then 1 else 0

public theorem get_ι_eq [DecidableEq ι] (i: ι) (a: α) : get i (.ι α i a) = a := by
  unfold get; rw [lift_ι, ite_eq_left rfl, smul_eq_mul, mul_one]
public theorem get_ι_ne [DecidableEq ι] (i j: ι) (h: i ≠ j) (a: α) : get i (.ι α j a) = 0 := by
  unfold get; rw [lift_ι, ite_eq_right h, smul_zero]

theorem contrapos {P Q: Prop} [ExcludedMiddle Q] (h: ¬Q -> ¬P) : P -> Q := by
  intro p; rcases em Q with q | nq
  assumption
  nomatch h nq p

theorem preDomain₀ [DecidableEq ι] [DecidableEq α] (lc: LinearCombo ι α) : ∃domain: List ι, ∀i, lc.get i ≠ 0 -> i ∈ domain := by
  induction lc with
  | zero =>
    exists []; intro i h
    rw [map_zero] at h
    contradiction
  | add a b iha ihb =>
    obtain ⟨da, hda⟩ := iha
    obtain ⟨db, hdb⟩ := ihb
    exists da ++ db
    intro i hi
    simp
    rw [map_add] at hi
    by_cases ha:get i a = 0
    rw [ha, zero_add] at hi
    right; apply hdb; assumption
    left; apply hda; assumption
  | ι j a =>
    exists [j]
    intro i hi
    by_cases h:i = j
    subst j
    rw [get_ι_eq] at hi; apply List.mem_singleton_self
    rw [get_ι_ne _ _ h] at hi
    contradiction

theorem preDomain₁ [DecidableEq ι] [DecidableEq α] (lc: LinearCombo ι α) : ∃domain: List ι, domain.Nodup ∧ (∀i, lc.get i ≠ 0 ↔ i ∈ domain) := by
  obtain ⟨domain, hdomain⟩ := preDomain₀ lc
  exists (domain.filter fun i => get i lc ≠ 0).eraseDups
  apply And.intro
  apply List.nodup_eraseDups
  intro i
  apply Iff.intro
  intro hi; simpa [hdomain _ hi]
  simp

public theorem domain [DecidableEq ι] [DecidableEq α] (lc: LinearCombo ι α) : ∃domain: List ι, domain.Nodup ∧ (∀i, lc.get i ≠ 0 ↔ i ∈ domain) ∧ lc = (domain.map (fun i => .ι α i (lc.get i))).sum := by
  induction lc with
  | zero =>
    exists []
    simp [map_zero]
  | ι i a =>
    by_cases ha:a = 0
    exists []
    simp [ha, map_zero]
    exists [i]; simp [add_zero, get_ι_eq]
    intro j
    apply Iff.intro
    intro hj
    apply Decidable.byContradiction
    intro h; rw [get_ι_ne _ _ h] at hj
    contradiction
    intro rfl; rwa [get_ι_eq]
  | add a b iha ihb =>
    have ⟨domain, domain_nodup, domain_spec⟩ := preDomain₁ (a + b)
    have ⟨da, da_nodup, da_spec, da_sum⟩ := iha
    have ⟨db, db_nodup, db_spec, db_sum⟩ := ihb
    clear iha ihb; refine ⟨domain, domain_nodup, domain_spec, ?_⟩
    simp [map_add]
    have : ∀x ∈ domain, x ∈ da ∨ x ∈ db := by
      intro i hi
      rw [←da_spec, ←db_spec]
      rw [←domain_spec, map_add] at hi
      apply Decidable.or_iff_not_imp_left.mpr
      intro g; simp at g; rwa [g, zero_add] at hi
    -- these sums are equal to the sums on supersets
    -- so we can extend all these sums to (da ∪ db)
    -- then merge the sums together
    sorry

@[ext] public theorem ext [DecidableEq ι] (a b: LinearCombo ι α) (h: ∀i, a.get i = b.get i) : a = b := by
  sorry
