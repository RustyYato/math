import LeanMath.Algebra.Monoid.Defs
import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Data.Trunc.Defs
import LeanMath.Data.LazyList.Defs
import LeanMath.Tactic.AxiomBlame
import LeanMath.Order.Defs

-- this support doesn't need to be minimal!
structure Finsupp.Spec {ι α: Type*} [Zero α] (f: ι -> α) where
  allowed_values: LazyList ι
  spec: ∀x, f x ≠ 0 -> x ∈ allowed_values
  nodup: Bool
  nodup_spec: nodup -> allowed_values.Nodup

structure Finsupp.Support {ι α: Type*} [Zero α] (f: ι -> α) where
  allowed_values: LazyList ι
  nodup: allowed_values.Nodup
  spec: ∀x, f x ≠ 0 -> x ∈ allowed_values

structure Finsupp (ι α: Type*) [Zero α] where
  toFun: ι -> α
  spec: Trunc (Finsupp.Spec toFun)

namespace Finsupp

def withNodupSupport
  [Zero α]
  (f: ι -> α)
  (support: LazyList ι)
  (nodup: support.Nodup)
  (spec: ∀i, f i ≠ 0 -> i ∈ support) : Finsupp ι α where
  toFun := f
  spec := Trunc.mk {
    allowed_values := support
    nodup := true
    nodup_spec _ := nodup
    spec := spec
  }

def withSupport
  [Zero α]
  (f: ι -> α)
  (support: LazyList ι)
  (spec: ∀i, f i ≠ 0 -> i ∈ support) : Finsupp ι α where
  toFun := f
  spec := Trunc.mk {
    allowed_values := support
    nodup := false
    nodup_spec := nofun
    spec := spec
  }

instance [Zero α] : FunLike (Finsupp ι α) ι α where
  coeInj := by
    intro a b h
    dsimp at h
    cases a; congr
    cases h; apply heq_of_eq
    apply Subsingleton.allEq

def single [DecidableEq ι] [Zero α] (i: ι) (a: α) : Finsupp ι α where
  toFun j := if i = j then a else 0
  spec := Trunc.mk {
    allowed_values := .singleton i
    spec := by
      intro i h
      split at h
      subst i; exists ⟨0, by simp⟩
      contradiction
    nodup := true
    nodup_spec := by
      intro _ _ _ _
      dsimp; apply Subsingleton.allEq
  }

def erase [DecidableEq ι] [Zero α] (i: ι) (f: Finsupp ι α) : Finsupp ι α where
  toFun j := if i = j then 0 else f j
  spec := f.spec.map fun supp => {
    allowed_values := supp.allowed_values
    spec := by
      intro i h
      apply supp.spec
      split at h
      contradiction
      assumption
    nodup := supp.nodup
    nodup_spec := supp.nodup_spec
  }

def set [DecidableEq ι] [Zero α] (i: ι) (a: α) (f: Finsupp ι α) : Finsupp ι α where
  toFun j := if i = j then a else f j
  spec := f.spec.map fun supp => {
    allowed_values := supp.allowed_values.cons i
    spec := by
      intro i h
      split at h
      simp; left; symm; assumption
      simp; right; apply supp.spec
      assumption
    nodup := false
    nodup_spec := nofun
  }

@[simp]
def apply_single [DecidableEq ι] [Zero α] (i: ι) (a: α) : single i a j = if i = j then a else 0 := rfl
@[simp]
def apply_erase [DecidableEq ι] [Zero α] (i: ι) (f: Finsupp ι α) : f.erase i j = if i = j then 0 else f j := rfl

instance [Zero α] : Zero (Finsupp ι α) where
  zero := {
    toFun _ := 0
    spec := Trunc.mk {
      allowed_values := .empty
      nodup := true
      nodup_spec := nofun
      spec := nofun
    }
  }

@[simp]
def single_zero [DecidableEq ι] [Zero α] (i: ι) : single i (0: α) = 0 := by
  apply DFunLike.ext
  intro i
  simp
  rfl

instance [Zero α] [SMul R α] [IsLawfulSMulZero R α] : SMul R (Finsupp ι α) where
  smul r f := {
    toFun x := r • f x
    spec := f.spec.map fun fsupp => {
      allowed_values := fsupp.allowed_values
      nodup := fsupp.nodup
      nodup_spec := fsupp.nodup_spec
      spec := by
        intro x hx
        apply fsupp.spec
        intro g
        apply hx
        rw [show f x = 0 from g, smul_zero]
    }
  }

@[simp] def apply_smul_single [Zero α] [SMul R α] [IsLawfulSMulZero R α] (r: R) (a: Finsupp ι α) : (r • a) j = r • (a j) := rfl

@[simp]
def smul_single [DecidableEq ι] [Zero α] [SMul R α] [IsLawfulSMulZero R α] (r: R) (i: ι) (a: α) : r • single i a = single i (r • a) := by
  apply DFunLike.ext; intro j
  simp
  split; rfl
  rw [smul_zero]

variable [ExcludedMiddleEq α] [ExcludedMiddleEq β]

instance instAdd [Add α] [Zero α] [IsLawfulZeroAdd α] : Add (Finsupp ι α) where
  add f g := {
    toFun x := f x + g x
    spec :=
      f.spec.bind fun fsupp =>
      g.spec.map fun gsupp => {
        allowed_values := fsupp.allowed_values ++ gsupp.allowed_values
        nodup :=
          bif fsupp.allowed_values.size == 0 then
            gsupp.nodup
          else bif gsupp.allowed_values.size == 0 then
            fsupp.nodup
          else
            false
        nodup_spec := by
          simp
          split <;> rename_i h₀
          intro h₁
          rw [LazyList.size_eq_zero] at h₀
          simpa [h₀] using gsupp.nodup_spec h₁
          intro ⟨h₁, h₂⟩
          rw [LazyList.size_eq_zero] at h₁
          simpa [h₁] using fsupp.nodup_spec h₂
        spec := by
          intro x h
          rw [LazyList.mem_append]
          rcases em (f x = 0) with hx | hx
          rw [hx, zero_add] at h
          right; apply gsupp.spec
          assumption
          left; apply fsupp.spec
          assumption
      }
  }

@[simp]
def apply_add [Add α] [Zero α] [IsLawfulZeroAdd α] (f g: Finsupp ι α) : (f + g) j = f j + g j := rfl

section

instance [AddMonoidOps α] [IsAddMonoid α] : IsAddMonoid (Finsupp ι α) where
  add_assoc _ _ _ := by
    apply DFunLike.ext; intro x
    apply add_assoc
  zero_add _ := by
    apply DFunLike.ext; intro x
    apply zero_add
  add_zero _ := by
    apply DFunLike.ext; intro x
    apply add_zero
  zero_nsmul _ := by
    apply DFunLike.ext; intro x
    apply zero_nsmul
  succ_nsmul _ _ := by
    apply DFunLike.ext; intro x
    apply succ_nsmul

instance [Zero α] [SMul R α] [IsLawfulSMulZero R α] [MonoidOps R] [IsMonoid R] [IsMonoidAction R α] : IsMonoidAction R (Finsupp ι α) where
  one_smul f := by
    apply DFunLike.ext; intro x
    apply one_smul
  mul_smul _ _ _ := by
    apply DFunLike.ext; intro x
    apply mul_smul

instance [SMul R α] [MonoidOps R] [IsMonoid R] [AddMonoidOps α] [IsAddMonoid α] [IsDistributiveAction R α] : IsDistributiveAction R (Finsupp ι α) where
  smul_zero _ := by
    apply DFunLike.ext; intro x
    apply smul_zero
  smul_add _ _ _ := by
    apply DFunLike.ext; intro x
    apply smul_add

instance [Add α] [Zero α] [IsAddComm α] [IsLawfulZeroAdd α] : IsAddComm (Finsupp ι α) where
  add_comm _ _ := by
    apply DFunLike.ext; intro x
    apply add_comm

end

def map [FunLike F α β] [Zero α] [Zero β] [IsZeroHom F α β] (f: F) : ZeroHom (Finsupp ι α) (Finsupp ι β) where
  toFun f₀ := {
    toFun := f ∘ f₀
    spec := f₀.spec.map fun supp => {
      allowed_values := supp.allowed_values
      nodup := supp.nodup
      nodup_spec := supp.nodup_spec
      spec := by
        intro x h
        dsimp at h
        apply supp.spec
        intro g; rw [show f₀ x = 0 from g, map_zero] at h
        contradiction
    }
  }
  map_zero := by
    apply DFunLike.ext
    intro i
    apply map_zero f

@[simp] def apply_map [FunLike F α β] [Zero α] [Zero β] [IsZeroHom F α β] (f: F) (f₀: Finsupp ι α) (i: ι) : map f f₀ i = f (f₀ i):= rfl

@[simp]
def map_single [DecidableEq ι] [FunLike F α β] [Zero α] [Zero β] [IsZeroHom F α β] (f: F) (i: ι) (a: α) : map f (single i a) = single i (f a) := by
  apply DFunLike.ext; intro j
  simp; split; rfl; rw [map_zero]

def support [DecidableEq ι] [Zero α] (f: Finsupp ι α) : Trunc (Finsupp.Support f) :=
  f.spec.map fun supp =>
  if h:supp.nodup then
    {
      allowed_values := supp.allowed_values
      nodup := supp.nodup_spec h
      spec := supp.spec
    }
  else
    {
      allowed_values := supp.allowed_values.basic_dedup
      nodup := LazyList.basic_dedup_nodup _
      spec := by
        intro i hi
        rw [LazyList.basic_dedup_mem]
        apply supp.spec
        assumption
    }

def simple_support [DecidableEq ι] [Zero α] (f: Finsupp ι α) : Trunc (Finsupp.Support f) :=
  f.spec.map fun supp =>
    {
      allowed_values := supp.allowed_values.basic_dedup
      nodup := LazyList.basic_dedup_nodup _
      spec := by
        intro i hi
        rw [LazyList.basic_dedup_mem]
        apply supp.spec
        assumption
    }

def support_eq_simple_supprt [DecidableEq ι] [Zero α] (f: Finsupp ι α) :
  f.support = f.simple_support := Subsingleton.allEq _ _

variable [DecidableEq ι]

def fold_with [Zero α] (f: ι -> α -> β -> β) (acc: β)
  (f₀: Finsupp ι α)
  (hzero: ∀i b, f₀ i = 0 -> f i 0 b = b) (hcomm: ∀i j a₀ a₁ b, f i a₀ (f j a₁ b) = f j a₁ (f i a₀ b)) : β :=
  f₀.support.lift (fun supp => supp.allowed_values.fold (fun i => f i (f₀ i)) acc) <| by
    intro supp₀ supp₁
    simp
    obtain ⟨supp₀, nodup₀, h₀⟩ := supp₀
    obtain ⟨supp₁, nodup₁, h₁⟩ := supp₁
    simp
    have h (i: ι) : f₀ i ≠ 0 -> (i ∈ supp₀ ↔ i ∈ supp₁) := by
      intro h
      simp [h₀ _ h, h₁ _ h]
    clear h₀ h₁
    induction supp₀ generalizing supp₁ with
    | nil =>
      simp
      induction supp₁ with
      | nil => simp
      | cons b bs ih =>
        simp
        have : f₀ b = 0 := by
          apply LEM.byContradiction
          intro g
          have := h _ g
          simp at this
        rw [this, hzero _ _ (by assumption)]
        apply ih
        exact LazyList.of_nodup_cons nodup₁
        intro i hi
        have := h i hi
        simp at this
        simp
        exact this.right
    | cons a as ih =>
      simp
      replace ih := ih (by
        apply LazyList.of_nodup_cons
        assumption)
      rcases em (f₀ a = 0) with ha | ha
      · rw [ha, hzero _ _ (by assumption)]
        apply ih
        · assumption
        · intro i hi
          rw [←h i hi]
          simp
          intro rfl
          contradiction
      · obtain ⟨supp₁, supp₂, rfl⟩ := (LazyList.mem_iff_append a supp₁).mp (by
          apply (h _ ha).mp
          simp)
        rw [LazyList.fold_comm_append _ _ (by
          intro i j b
          rw [hcomm])]
        simp
        congr 1; apply ih
        · have := nodup₁.append_comm
          rw [LazyList.cons_append] at this
          exact this.tail
        · intro i hi
          replace h := h i hi
          simp at h
          simp
          apply Iff.intro
          · intro g
            rcases h.mp (.inr g) with h | rfl | h
            · right; assumption
            · have := nodup₀.head
              contradiction
            · left; assumption
          · intro g
            have := nodup₁.append_comm
            rw [LazyList.cons_append] at this
            replace this := this.head
            simp at this
            obtain ⟨_, _⟩ := this
            rcases g with g | g
            · rcases h.mpr (.inr (.inr g)) with rfl | h
              · contradiction
              · assumption
            · rcases h.mpr (.inl g) with rfl | h
              · contradiction
              · assumption

def fold [Zero α] (f: α -> β -> β) (acc: β) (hzero: ∀b, f 0 b = b) (hcomm: ∀a₀ a₁ b, f a₀ (f a₁ b) = f a₁ (f a₀ b)) (f₀: Finsupp ι α) : β :=
  f₀.support.lift (fun supp => supp.allowed_values.fold (f ∘ f₀) acc) <| by
    intro supp₀ supp₁
    simp
    obtain ⟨supp₀, nodup₀, h₀⟩ := supp₀
    obtain ⟨supp₁, nodup₁, h₁⟩ := supp₁
    simp
    have h (i: ι) : f₀ i ≠ 0 -> (i ∈ supp₀ ↔ i ∈ supp₁) := by
      intro h
      simp [h₀ _ h, h₁ _ h]
    clear h₀ h₁
    induction supp₀ generalizing supp₁ with
    | nil =>
      simp
      induction supp₁ with
      | nil => simp
      | cons b bs ih =>
        simp
        have : f₀ b = 0 := by
          apply LEM.byContradiction
          intro g
          have := h _ g
          simp at this
        rw [this, hzero]
        apply ih
        exact LazyList.of_nodup_cons nodup₁
        intro i hi
        have := h i hi
        simp at this
        simp
        exact this.right
    | cons a as ih =>
      simp
      replace ih := ih (by
        apply LazyList.of_nodup_cons
        assumption)
      rcases em (f₀ a = 0) with ha | ha
      · rw [ha, hzero]
        apply ih
        · assumption
        · intro i hi
          rw [←h i hi]
          simp
          intro rfl
          contradiction
      · obtain ⟨supp₁, supp₂, rfl⟩ := (LazyList.mem_iff_append a supp₁).mp (by
          apply (h _ ha).mp
          simp)
        rw [LazyList.fold_comm_append (f ∘ f₀) _ (by
          intro i j b
          simp
          rw [hcomm])]
        simp
        congr 1; apply ih
        · have := nodup₁.append_comm
          rw [LazyList.cons_append] at this
          exact this.tail
        · intro i hi
          replace h := h i hi
          simp at h
          simp
          apply Iff.intro
          · intro g
            rcases h.mp (.inr g) with h | rfl | h
            · right; assumption
            · have := nodup₀.head
              contradiction
            · left; assumption
          · intro g
            have := nodup₁.append_comm
            rw [LazyList.cons_append] at this
            replace this := this.head
            simp at this
            obtain ⟨_, _⟩ := this
            rcases g with g | g
            · rcases h.mpr (.inr (.inr g)) with rfl | h
              · contradiction
              · assumption
            · rcases h.mpr (.inl g) with rfl | h
              · contradiction
              · assumption

def map_fold
  [FunLike F α β] [Zero α] [Zero β] [IsZeroHom F α β]
  (f: F) (g: β -> γ -> γ)
  (acc: γ) (hzero: ∀b: γ, g 0 b = b) (hcomm: ∀a₀ a₁ b, g a₀ (g a₁ b) = g a₁ (g a₀ b))
  (f₀: Finsupp ι α)
  : (f₀.map f).fold g acc hzero hcomm = f₀.fold (g ∘ f) acc (by
    intro x
    simp [map_zero, hzero]) (by
    intro _ _ _
    simp [hcomm]) := by
    unfold fold
    obtain ⟨f₀, supp⟩ := f₀
    induction supp with | mk supp =>
    conv => { lhs; rhs; simp [map, support] }
    conv => { rhs; rhs; simp [support] }
    show LazyList.fold _ _ _ =  LazyList.fold _ _ _
    simp
    congr
    split
    rfl
    rfl

@[simp]
def fold_single [DecidableEq ι] [Zero α] (f: α -> β -> β) (acc: β) (hzero: ∀b, f 0 b = b) (hcomm: ∀a₀ a₁ b, f a₀ (f a₁ b) = f a₁ (f a₀ b))
  (i: ι)
  : fold f acc hzero hcomm (.single i a) = f a acc := by
  simp [single, fold, support]
  show f (if _ then _ else _) _ = _
  rw [if_pos rfl]

section

variable [AddMonoidOps α] [IsAddComm α] [IsAddMonoid α]
variable [AddMonoidOps β] [IsAddComm β] [IsAddMonoid β]

def single_add_erase_eq_self [DecidableEq ι] (f: Finsupp ι α) (i: ι) : single i (f i) + f.erase i = f := by
  apply DFunLike.ext; intro j
  by_cases h:i = j
  subst j
  simp [add_zero]
  simp [zero_add, if_neg h]

private def preSum (f: Finsupp ι α) : α :=
  f.fold (· + ·) 0 (by
    intro a
    dsimp; rw [zero_add]) <| by
      intro a₀ a₁ a₂
      dsimp
      rw [← add_assoc, add_comm a₀, add_assoc]

private def compute_basis (f: Finsupp ι α) : Finsupp ι α -> LazyList ι -> Finsupp ι α :=
  LazyList.fold (fun i acc => single i (f i) + acc)

@[simp]
private def compute_basis_nil (f acc: Finsupp ι α) :
  compute_basis f acc (.empty) = acc := rfl

@[simp]
private def compute_basis_cons (f acc: Finsupp ι α) (a: ι) (as: LazyList ι) :
  compute_basis f acc (.cons a as) = single a (f a) + compute_basis f acc as := by
  unfold compute_basis
  rw [LazyList.fold_cons]

def compute_basis_acc (f acc: Finsupp ι α) (as: LazyList ι) :
  compute_basis f acc as = acc + compute_basis f 0 as := by
  induction as with
  | nil => simp [add_zero]
  | cons a as ih =>
    simp
    rw [←add_assoc, add_comm acc, add_assoc, ih]

def compute_basis_append (f: Finsupp ι α) (as bs: LazyList ι) :
  compute_basis f 0 (as ++ bs) = compute_basis f 0 as + compute_basis f 0 bs := by
  induction as with
  | nil => simp [zero_add]
  | cons a as ih => simp [ih, add_assoc]

def compute_basis_congr (f g: Finsupp ι α) (as: LazyList ι) :
  (∀i ∈ as, f i = g i) ->
  compute_basis f 0 as = compute_basis g 0 as := by
  intro hi
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp; rw [ih]
    congr 2
    apply hi
    simp
    intro i h
    apply hi
    simp [h]

private def exists_basis (f: Finsupp ι α) :
  ∃as: LazyList ι, as.Nodup ∧ f = compute_basis f 0 as := by
  have supp := f.support
  induction supp with | mk supp =>
  obtain ⟨supp, nodup, hsupp⟩ := supp
  exists supp
  apply And.intro
  assumption
  induction supp generalizing f with
  | nil =>
    simp; apply DFunLike.ext
    intro i
    apply LEM.byContradiction
    intro h
    nomatch hsupp i h
  | cons a as ih =>
    rw (occs := [1]) [←single_add_erase_eq_self f a, ih (f.erase a) nodup.tail]
    simp; congr 1
    · apply compute_basis_congr
      intro i hi
      simp; intro rfl
      have := nodup.head
      contradiction
    · intro i hi
      simp at hi
      have := hsupp i hi.right
      simpa [Ne.symm hi.left] using this

@[induction_eliminator]
def list_induction
  {motive: Finsupp ι α -> Prop}
  (zero: motive 0)
  (single_add: ∀i a f, f i = 0 -> motive f -> motive (.single i a + f))
  (f: Finsupp ι α) : motive f := by
  have supp := f.support
  induction supp with | mk supp =>
  obtain ⟨supp, nodup, hsupp⟩ := supp
  induction supp generalizing f with
  | nil =>
    suffices f = 0 by
      subst f
      apply zero
    apply DFunLike.ext
    intro i
    apply LEM.byContradiction
    intro h
    nomatch hsupp i h
  | cons a as ih =>
    rw (occs := [1]) [←single_add_erase_eq_self f a]
    apply single_add
    simp
    apply ih
    exact nodup.tail
    intro i hi
    simp at hi
    simpa [Ne.symm hi.left] using hsupp _ hi.right

@[induction_eliminator]
def induction
  {motive: Finsupp ι α -> Prop}
  (zero: motive 0)
  (single: ∀i a, motive (.single i a))
  (add: ∀f g, motive f -> motive g -> motive (f + g))
  (f: Finsupp ι α) : motive f := by
  induction f using list_induction with
  | zero => apply zero
  | single_add =>
    apply add
    apply single
    assumption

@[simp]
private def preSum_single (i: ι) (a: α) : preSum (.single i a) = a := by
  unfold preSum
  rw [fold_single, add_zero]

def single_add (i: ι) (a b: α) : single i a + single i b = single i (a + b) := by
  apply DFunLike.ext
  intro j
  simp
  split
  rfl
  rw [add_zero]

def sum : Finsupp ι α →+ α where
  toFun := preSum
  map_zero := rfl
  map_add f g := by
    simp [preSum, fold]
    rw [support_eq_simple_supprt, simple_support]
    conv => {
      lhs; arg 3; arg 2; simp [HAdd.hAdd, Add.add]
    }
    induction f.spec with | mk fspec =>
    induction g.spec with | mk gspec =>
    simp
    rw [show f.support = Trunc.mk {
      allowed_values := (fspec.allowed_values ++ gspec.allowed_values).basic_dedup
      nodup := LazyList.basic_dedup_nodup _
      spec := ?_
    } from ?_]
    rw [show g.support = Trunc.mk {
      allowed_values := (fspec.allowed_values ++ gspec.allowed_values).basic_dedup
      nodup := LazyList.basic_dedup_nodup _
      spec := ?_
    } from ?_]
    simp
    generalize (fspec.allowed_values ++ gspec.allowed_values).basic_dedup=as
    · induction as with
      | nil => simp [add_zero]
      | cons a as ih =>
        simp [ih]
        ac_rfl
    · intro i hi
      simp [LazyList.basic_dedup_mem]
      right; apply gspec.spec
      assumption
    · apply Subsingleton.allEq
    · intro i hi
      simp [LazyList.basic_dedup_mem]
      left; apply fspec.spec
      assumption
    · apply Subsingleton.allEq

def mapHom [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (f: F) : Finsupp ι α →+ Finsupp ι β where
  toZeroHom := map f
  map_add := by
    intro a b
    apply DFunLike.ext; intro j
    apply map_add f

def map_eq_mapHom [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (f: F) (f₀: Finsupp ι α): map f f₀ = mapHom f f₀ := rfl

@[simp]
def sum_single (i: ι) (a: α) : sum (single i a) = a := preSum_single _ _

def map_sum [LEM] [DecidableEq β] [FunLike F α β] [IsZeroHom F α β] [IsAddHom F α β] (f: F) (f₀: Finsupp ι α) : (f₀.map f).sum = f f₀.sum := by
  induction f₀ with
  | zero => repeat rw [map_zero]
  | single => simp
  | add a b iha ihb =>
    simp [map_add, map_eq_mapHom]
    simp [←map_eq_mapHom, iha, ihb]

def sumHom [LEM] [SMul R α] [MonoidOps R] [IsMonoid R] [IsDistributiveAction R α] : Finsupp ι α →ₗ[R] α where
  toAddHom := sum.toAddHom
  map_smul := by
    intro r a
    show sum (r • a) = r • sum a
    induction a with
    | zero => simp [smul_zero, map_zero]
    | single => simp
    | add _ _ iha ihb => simp [smul_add, map_add, iha, ihb]

end

end Finsupp
