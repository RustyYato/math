module

public import Math.Algebra.DirectSum.Defs
public import Math.Algebra.Module.Defs.Basic
public import Math.Algebra.Module.Hom.Defs
-- public import Math.Data.Finset.Defs
public import Math.Data.Finset.Algebra
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

theorem preDomain₂ [DecidableEq ι] [DecidableEq α] (lc: LinearCombo ι α) : ∃domain: Finset ι, (∀i, lc.get i ≠ 0 ↔ i ∈ domain) := by
  obtain ⟨domain, domain_nodup, hdomain⟩ := preDomain₁ lc
  exact ⟨⟨.mk domain, domain_nodup⟩, hdomain⟩

def IsDomain [DecidableEq ι] (s: Finset ι) (lc: LinearCombo ι α) : Prop := ∀i, lc.get i ≠ 0 -> i ∈ s

@[expose] public def domain_sum [DecidableEq ι] (s: Finset ι) (lc: LinearCombo ι α) : LinearCombo ι α :=
  s.sum fun i => .ι α i (lc.get i)

@[simp] public theorem domain_sum_empty [DecidableEq ι] (lc: LinearCombo ι α) : domain_sum ∅ lc = 0 :=
  Finset.sum_empty _

@[simp] public theorem domain_sum_insert_unique [DecidableEq ι] (i: ι) (s: Finset ι) (hi: i ∉ s) (lc: LinearCombo ι α) : domain_sum (s.insert_unique i hi) lc = .ι α i (lc.get i) + domain_sum s lc :=
  Finset.sum_insert_unique _ _ _ _

instance [Add β] [IsAddComm β] : Std.Commutative (α := β) (· + ·) where
  comm _ _ := add_comm _ _
instance [Add β] [IsAddSemigroup β] : Std.Associative (α := β) (· + ·) where
  assoc := add_assoc

theorem domain_sum_add [DecidableEq ι]
  (s: Finset ι)
  (a b: LinearCombo ι α) : domain_sum s (a + b) = domain_sum s a + domain_sum s b := by
  unfold domain_sum
  induction s generalizing a b with
  | nil => simp [add_zero]
  | cons i s not_mem ih =>
    simp
    rw [ih]
    simp [map_add]
    ac_rfl

theorem domain_sum_disjoint [DecidableEq ι] (s t: Finset ι) (h: ∀x, x ∉ s ∩ t) (lc: LinearCombo ι α) :
  domain_sum (s ∪ t) lc = domain_sum s lc + domain_sum t lc := by
  unfold domain_sum
  induction s with
  | nil => simp [zero_add]
  | cons a as a_not_in_as ih =>
    simp; rw [add_assoc, Finset.insert_unique_union]
    simp; congr 1
    rw [ih]
    · intro i
      have := h i
      simp at this
      simp; intro h; apply this;
      right; assumption
    · have := h a
      simpa

theorem domain_sum_eq_superset [DecidableEq ι] [ExcludedMiddleEq α]
  (s t: Finset ι) (h: s ⊆ t)
  (lc: LinearCombo ι α) (hs: IsDomain s lc) : domain_sum s lc = domain_sum t lc := by
  obtain ⟨t, rfl, ht⟩ := Finset.eq_union_of_superset h; clear h
  rw [←add_zero (domain_sum s lc), domain_sum_disjoint _ _ ht]
  congr; symm
  have : ∀i ∈ t, lc.get i = 0 := ?_
  · unfold domain_sum
    clear s ht hs
    induction t with
    | nil => rw [Finset.sum_empty]
    | cons _ _ _ ih =>
      rw [Finset.sum_insert_unique, this, map_zero, zero_add, ih]
      intro i hi
      apply this; simp; right; assumption
      simp
  · intro i hi
    apply LEM.byContradiction
    intro g
    apply ht i
    simp [hi]
    apply hs
    assumption

public theorem domain [DecidableEq ι] [DecidableEq α] (lc: LinearCombo ι α) :
  ∃domain: Finset ι, (∀i, lc.get i ≠ 0 ↔ i ∈ domain) ∧ lc = domain_sum domain lc := by
  induction lc with
  | zero =>
    exists ∅
    simp [map_zero, domain_sum]
  | ι i a =>
    by_cases ha:a = 0
    exists ∅
    simp [ha, map_zero, domain_sum]
    exists {i}; simp [get_ι_eq, domain_sum]
    intro j
    apply Iff.intro
    intro hj
    apply Decidable.byContradiction
    intro h; rw [get_ι_ne _ _ h] at hj
    contradiction
    intro rfl; rwa [get_ι_eq]
  | add a b iha ihb =>
    have ⟨domain, domain_nodup, domain_spec⟩ := preDomain₁ (a + b)
    have ⟨da, da_spec, da_sum⟩ := iha
    have ⟨db, db_spec, db_sum⟩ := ihb
    clear iha ihb; refine ⟨⟨.mk domain, domain_nodup⟩, domain_spec, ?_⟩
    have : ∀x ∈ domain, x ∈ da ∪ db := by
      intro i hi; simp
      rw [←da_spec, ←db_spec]
      rw [←domain_spec, map_add] at hi
      apply Decidable.or_iff_not_imp_left.mpr
      intro g; simp at g; rwa [g, zero_add] at hi
    rw (occs := [1]) [da_sum, db_sum]
    have ha : IsDomain da a := by
      intro i hi
      exact (da_spec i).mp hi
    have hb : IsDomain db b := by
      intro i hi
      exact (db_spec i).mp hi
    rw [
      domain_sum_eq_superset (s := da) (t := da ∪ db),
      domain_sum_eq_superset (s := db) (t := da ∪ db),
      domain_sum_eq_superset (s := Finset.mk (Multiset.mk domain) domain_nodup) (t := da ∪ db),
    ]
    · rw [domain_sum_add]
    · apply this
    · intro i hi
      apply (domain_spec i).mp
      assumption
    · intro i; simp; apply Or.inr
    · assumption
    · intro i; simp; apply Or.inl
    · assumption

@[ext] public theorem ext [DecidableEq ι] [DecidableEq α] (a b: LinearCombo ι α) (h: ∀i, a.get i = b.get i) : a = b := by
  have ⟨da, da_spec, ha⟩ := domain a
  have ⟨db, db_spec, hb⟩ := domain b
  rw [ha, hb]; clear ha hb
  rw [show da = db from ?_]
  unfold domain_sum; congr; ext i
  rw [h]
  ext i; rw [←da_spec, ←db_spec, h]
