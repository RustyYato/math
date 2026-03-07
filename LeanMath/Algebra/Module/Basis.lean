import LeanMath.Algebra.Monoid.Action.Set
import LeanMath.Data.LinearCombo.Module

variable (R: Type*) [SMul R α]
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α] [IsAddComm α]
  [IsModule R α]

namespace Submodule

def eval {U: Set α} : LinearCombo R U →ₗ[R] α := LinearCombo.liftLin Subtype.val

@[simp] def eval_ι {U: Set α} (a: U) (r: R) : eval R (LinearCombo.ι a r) = r • a.val := LinearCombo.liftLin_ι _ _ _

-- linear independence means that the only linear combination
-- that evaluates to 0, is the 0 linear combination
def IsLinindep (U: Set α) := ∀lc: LinearCombo R U, eval R lc = 0 -> lc = 0

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

def upcast (U V: Set α) (h: U ⊆ V) : LinearCombo R U →ₗ[R] LinearCombo R V :=
  liftLin fun x => LinearCombo.ι ⟨x.val, h _ x.property⟩ 1

@[simp]
def upcast_ι (U V: Set α) (h: U ⊆ V) (a: U) (r: R) : upcast R U V h (ι a r) = ι ⟨a, h _ a.property⟩ r := by
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
    congr; rw [if_pos]
    symm; apply Subtype.val_inj; assumption
    rw [if_neg, map_zero]
    rintro rfl
    contradiction

end LinearCombo
