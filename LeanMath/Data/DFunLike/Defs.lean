import LeanMath.Algebra.Monoid.Defs
import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Data.Trunc.Defs
import LeanMath.Data.Fintype.Defs
import LeanMath.Tactic.AxiomBlame
import LeanMath.Order.Defs

class FinsuppSupportLike (S: Type*) (ι: outParam Sort*) extends Max S, Inhabited S where
  card: S -> ℕ
  get (s: S) (idx: Fin (card s)): ι
  get_max_left (a b i): ∃j, get a i = get (a ⊔ b) j
  get_max_right (a b i): ∃j, get b i = get (a ⊔ b) j
  singleton: ι -> S
  mem_singleton (i: ι): ∃j, get (singleton i) j = i

structure NatRange where
  lo: ℕ
  hi: ℕ
  lo_le_hi: lo ≤ hi

instance : FinsuppSupportLike ℕ ℕ where
  card := id
  get n idx := idx.val
  get_max_left := by
    intro a b i
    exists i.castLE ?_
    apply left_le_max
    rfl
  get_max_right := by
    intro a b i
    exists i.castLE ?_
    apply right_le_max
    rfl
  singleton x := x + 1
  mem_singleton _ := by exists Fin.last _

def NatRange.is_empty (range: NatRange) : Bool := range.lo == range.hi

instance : Membership Nat NatRange where
  mem r n := r.lo ≤ n ∧ n < r.hi

instance : Max NatRange where
  max a b :=
    if a.is_empty then
      b
    else if b.is_empty then
      a
    else
    {
      lo := a.lo ⊓ b.lo
      hi := a.hi ⊔ b.hi
      lo_le_hi := by
        apply le_trans min_le_left
        apply le_trans _ left_le_max
        exact a.lo_le_hi
    }

instance : FinsuppSupportLike NatRange ℕ where
  default := {
    lo := 0
    hi := 0
    lo_le_hi := Nat.le_refl _
  }
  card r := r.hi - r.lo
  get s i := s.lo + i.val
  get_max_left a b i := by
    have : a.is_empty = false := by
      simp [NatRange.is_empty]
      intro h
      rw [h, Nat.sub_self] at i
      exact i.elim0
    simp [Max.max, this]
    cases b.is_empty <;> simp
    · refine ⟨⟨i.val + a.lo - (a.lo ⊓ b.lo), ?_⟩, ?_⟩
      simp [this]
      split
      omega
      omega
      dsimp
      omega
    · exists ⟨i, ?_⟩
      simp [this]; rfl
  get_max_right a b i := by
    have : b.is_empty = false := by
      simp [NatRange.is_empty]
      intro h
      rw [h, Nat.sub_self] at i
      exact i.elim0
    simp [Max.max, this]
    cases a.is_empty <;> simp
    · refine ⟨⟨i.val + b.lo - (a.lo ⊓ b.lo), ?_⟩, ?_⟩
      simp [this]
      split
      omega
      omega
      dsimp
      omega
    · exists ⟨i, ?_⟩
      simp; rfl
  singleton i := {
    lo := i
    hi := i + 1
    lo_le_hi := Nat.le_succ _
  }
  mem_singleton := by
    intro i
    dsimp; exists ⟨0, by simp⟩

structure DFinsupp.Spec {ι: Sort*} (A: ι -> Type*) (S: Type*) [FinsuppSupportLike S ι] [∀i, Zero (A i)] (toFun: ∀i, A i) where
  set: S
  nonzero_mem: ∀i: ι, toFun i ≠ 0 -> ∃j, FinsuppSupportLike.get set j = i

structure DFinsupp {ι: Sort*} (A: ι -> Type*) (S: Type*) [FinsuppSupportLike S ι] [∀i, Zero (A i)] where
  toFun: ∀i, A i
  spec: Trunc (DFinsupp.Spec A S toFun)

namespace DFinsupp

section

variable [FinsuppSupportLike S ι] {A B C: ι -> Type*}

instance [∀i: ι, Zero (A i)] [FinsuppSupportLike S ι] : DFunLike (DFinsupp A S) ι A where
  coeInj := by
    intro a b h
    cases a
    congr; apply Subsingleton.helim
    congr

def DFinsupp.merge_pairwise [∀i, Zero (A i)] [∀i, Zero (B i)] [∀i, Zero (C i)]
  (f: { f: ∀i, A i -> B i -> C i // ∀{i a b}, f i a b ≠ 0 -> a ≠ 0 ∨ b ≠ 0 })
  (a: DFinsupp A S) (b: DFinsupp B S): DFinsupp C S where
  toFun i := f.val i (a i) (b i)
  spec :=
    a.spec.bind fun sa =>
    b.spec.map fun sb => {
      set := sa.set ⊔ sb.set
      nonzero_mem := by
        intro i hi
        rcases f.property hi with h | h
        · have ⟨ia, hia⟩ := sa.nonzero_mem _ h
          have ⟨ja, hja⟩ := FinsuppSupportLike.get_max_left sa.set sb.set ia
          exists ja
          rw [←hja, hia]
        · have ⟨ia, hia⟩ := sb.nonzero_mem _ h
          have ⟨ja, hja⟩ := FinsuppSupportLike.get_max_right sa.set sb.set ia
          exists ja
          rw [←hja, hia]
    }

end

variable {ι: Type*} [FinsuppSupportLike S ι] {A B C: ι -> Type*}
   [∀i, DecidableEq (A i)]

instance [∀i, Zero (A i)] : Zero (DFinsupp A S) where
  zero := {
    toFun _ := 0
    spec := Trunc.mk {
      set := default
      nonzero_mem := nofun
    }
  }

@[simp] def apply_zero [∀i, Zero (A i)] : (0: DFinsupp A S) i = 0 := rfl

@[ext] def ext [∀i, Zero (A i)] (a b: DFinsupp A S) (h: ∀i, a i = b i) : a = b := DFunLike.ext _ _ h

section

variable [∀i, Zero (A i)] [∀i, Add (A i)] [∀i, IsLawfulZeroAdd (A i)]

instance instAdd : Add (DFinsupp A S) where
  add := DFinsupp.merge_pairwise {
    val _ a b := a + b
    property {i a b} h := by
      dsimp; dsimp at h
      apply Decidable.or_iff_not_imp_left.mpr
      rw [Decidable.not_not]
      intro ha; rwa [ha, zero_add] at h
  }

@[simp] def apply_add (a b: DFinsupp A S) : (a + b) i = a i + b i := rfl

end

section

variable [∀i, Zero (A i)] [∀i, SMul R (A i)] [∀i, IsLawfulSMulZero R (A i)] [MonoidOps R] [IsMonoid R] [∀i, IsMonoidAction R (A i)]

instance instSMul : SMul R (DFinsupp A S) where
  smul r f := {
      toFun i := r • f i
      spec := f.spec.map fun s => {
        set := s.set
        nonzero_mem := by
          intro i hi
          have : f i ≠ 0 := by
            intro h; rw [h] at hi
            rw [smul_zero] at hi
            contradiction
          exact s.nonzero_mem _ this
      }
  }

@[simp] def apply_smul (r: R) (f: DFinsupp A S) : (r • f) i = r • f i := rfl

end

instance [∀i, AddMonoidOps (A i)] [∀i, IsAddMonoid (A i)] : IsAddMonoid (DFinsupp A S) where
  add_assoc _ _ _ := by ext; apply add_assoc
  zero_add _ := by ext; apply zero_add
  add_zero _ := by ext; apply add_zero
  zero_nsmul _ := by ext; apply zero_nsmul
  succ_nsmul _ _ := by ext; apply succ_nsmul

variable [DecidableEq ι]

def single [∀i, Zero (A i)] (i: ι) (val: A i) : DFinsupp A S where
  toFun j := if h:j = i then cast (h ▸ rfl) val else 0
  spec := Trunc.mk {
    set := FinsuppSupportLike.singleton i
    nonzero_mem := by
      intro a h
      split at h
      subst a
      have ⟨j, hj⟩ := FinsuppSupportLike.mem_singleton (S := S) i
      exists j
      contradiction
  }

def erase [∀i, Zero (A i)] (i: ι) (f: DFinsupp A S) : DFinsupp A S where
  toFun j := if j = i then 0 else f j
  spec :=
  f.spec.map fun s => {
    set := s.set
    nonzero_mem := by
      intro a h
      split at h
      contradiction
      exact s.nonzero_mem _ h
  }

@[simp] def apply_single [∀i, Zero (A i)] (i j: ι) (val: A i) : single (S := S) i val j = (if h:j = i then cast (h ▸ rfl) val else 0: A j) := rfl
@[simp] def apply_erase [∀i, Zero (A i)] (i j: ι) (f: DFinsupp A S) : f.erase i j = (if j = i then 0 else f j) := rfl

def single_add_erase
  [∀i, Zero (A i)] [∀i, Add (A i)]
  [∀i, IsLawfulZeroAdd (A i)]
  (i: ι) (f: DFinsupp A S) :
  single i (f i) + f.erase i = f := by
  ext j; simp
  split
  rw [add_zero]; subst j; rfl
  rw [zero_add]

end DFinsupp
