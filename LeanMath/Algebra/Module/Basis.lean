import LeanMath.Algebra.Monoid.Action.Set
import LeanMath.Algebra.Ring.Module.Defs
import LeanMath.Data.LinearCombo.Module
import LeanMath.Data.LinearCombo.AddGroup

namespace Submodule

variable (R: Type*) [SMul R α]
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  [IsModule R α]

def eval {U: Set α} : LinearCombo R U →ₗ[R] α := LinearCombo.liftLin Subtype.val

@[simp] def eval_ι {U: Set α} (a: U) (r: R) : eval R (LinearCombo.ι a r) = r • a.val := LinearCombo.liftLin_ι _ _ _

-- linear independence means that the evaluation
-- function from formal linear combinations to the
-- ground set of vectors is injective.
-- If the vectors form a group (instead of just a monoid)
-- this is equivalent to saying that eval a = 0 -> a = 0
def IsLinindep (U: Set α) :=
  Function.Injective (eval R (U := U))

-- a basis is is a linearly independent spanning set
structure IsBasis (U: Set α) : Prop where
  spanning_set: IsSpanningSet R U
  linindep: IsLinindep R U

def lincombo_mem_span_of_subset {U: Set α} (lc: LinearCombo R U) (s: Submodule R α) (h: U ⊆ s) : eval R lc ∈ s := by
  induction lc with
  | zero => rw [map_zero]; apply mem_zero
  | add => rw [map_add]; apply mem_add <;> assumption
  | ι a r =>
    rw [eval_ι]
    apply mem_smul
    apply h
    exact a.property

end Submodule

namespace LinearCombo

variable (R: Type*) [SMul R α]
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  [IsModule R α]

def upcast (U V: Set α) (h: U ⊆ V) : LinearCombo R U →ₗ[R] LinearCombo R V :=
  liftLin fun x => LinearCombo.ι ⟨x.val, h _ x.property⟩ 1

@[simp]
def upcast_ι (U V: Set α) (h: U ⊆ V) (a: U) (r: R) : upcast R U V h (ι a r) = ι ⟨a.val, h _ a.property⟩ r := by
  rw [upcast, LinearCombo.liftLin_ι, smul_ι]
  congr; apply mul_one

def filter (U V: Set α) [∀x, Decidable (x ∈ V)] : LinearCombo R U →ₗ[R] LinearCombo R V :=
  liftLin fun x =>
    if hx:x.val ∈ V then
      LinearCombo.ι ⟨x.val, hx⟩ 1
    else
      0

def filter_ι (U V: Set α) [∀x, Decidable (x ∈ V)] (a: U) (r: R) : filter R U V (ι a r) =
  if h:a.val ∈ V then ι ⟨_, h⟩ r else 0 := by
  rw [filter, LinearCombo.liftLin_ι]
  split
  rw [smul_ι]
  congr; apply mul_one
  rw [smul_zero]

def filter_add_union (U V₀ V₁: Set α) [∀x, Decidable (x ∈ V₀)] [∀x, Decidable (x ∈ V₁)] (hunion: V₀ ∪ V₁ = U) (hdisjoint: V₀ ∩ V₁ = ⊥) (l: LinearCombo R U) :
  l = upcast R _ U (by rw [←hunion]; intro; exact .inl) (filter R U V₀ l) + upcast R _ U (by rw [←hunion]; intro; exact .inr) (filter R U V₁ l) := by
  induction l with
  | zero => simp [map_zero, add_zero]
  | add a b iha ihb =>
    simp [map_add]
    rw [add_assoc, add_comm (upcast _ _ _ _ (filter _ _ _ b)), ←add_assoc, ←add_assoc,
      ←iha, add_assoc, add_comm (upcast _ _ _ _ _), ←ihb]
  | ι a r =>
    rw [filter_ι, filter_ι]
    split <;> rename_i h
    rw [dif_neg, map_zero, upcast_ι, add_zero]
    intro g
    have : a.val ∈ V₀ ∩ V₁ := by simp [h, g]
    rw [hdisjoint] at this
    contradiction
    rw [map_zero, dif_pos, zero_add, upcast_ι]
    have : a.val ∈ V₀ ∪ V₁ := hunion ▸ a.property
    simpa [h] using this

def upcast_eval (U V: Set α) (h: U ⊆ V) (lc: LinearCombo R U) : Submodule.eval R (upcast R U V h lc) = Submodule.eval R lc := by
  induction lc with
  | zero => simp [map_zero]
  | add => simp [map_add]; congr
  | ι a r => simp

def filter_singleton {U: Set α} [DecidableEq α] (a: α) (ha: a ∈ U) (lc: LinearCombo R U) :
  filter R U ({a}: Set α) lc = LinearCombo.ι ⟨a, rfl⟩ (LinearCombo.get ⟨a, ha⟩ lc) := by
  induction lc with
  | zero => simp [map_zero]
  | add a b iha ihb => simp [map_add]; congr
  | ι a' r =>
    simp [filter_ι, get_ι]
    split <;> rename_i h
    symm; congr; rw [if_pos]
    apply Subtype.val_inj; assumption
    rw [if_neg, map_zero]
    rintro rfl
    contradiction

def filter_upcast_filter
  (U V₀ V₁: Set α)
  [∀x, Decidable (x ∈ V₀)]
  [∀x, Decidable (x ∈ V₁)]
  (hsub₀: V₀ ⊆ V₁)
  (hsub₁: V₁ ⊆ U)
  (lc: LinearCombo R U) :
  upcast R V₁ U hsub₁ (filter R U V₁ (upcast R V₀ U (Set.sub_trans hsub₀ hsub₁) (filter R U V₀ lc)))
  = upcast R V₀ U (Set.sub_trans hsub₀ hsub₁) (filter R U V₀ lc) := by
  induction lc with
  | zero => simp [map_zero]
  | add a b iha ihb => simp [map_add, iha, ihb]
  | ι a r =>
    rw [filter_ι]
    split <;> rename_i h
    simp [upcast_ι, filter_ι, dif_pos (hsub₀ _ h)]
    simp [map_zero]

def filter_eval_from_basis_mem
  (U V: Set α)
  [∀x, Decidable (x ∈ V)]
  (basis: List (U × R))
  (hbasis: ∀x ∈ basis, x.fst.val ∈ V)
  : Submodule.eval R (from_elements basis) =
  Submodule.eval R (filter R U V (from_elements basis)) := by
  induction basis with
  | nil => simp [map_zero]
  | cons v vs ih =>
    simp [map_add, filter_ι]; rw [dif_pos, Submodule.eval_ι]; congr 1
    apply ih
    intro x hx; apply hbasis
    simp [hx]
    apply hbasis
    simp

end LinearCombo

namespace LinearCombo

variable (R: Type*) [SMul R α]
  [RingOps R] [IsRing R]
  [AddGroupOps α] [IsAddGroup α] [IsAddComm α]
  [IsModule R α]

end LinearCombo
