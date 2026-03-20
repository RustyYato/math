import LeanMath.Order.Defs
import LeanMath.Data.Fintype.Defs


def max_of_range_with [Fintype ι] [LE α] [LT α] [Max α] [IsSemiLatticeMax α]
  (f: ι -> α) (bot: α) : α :=
  Fintype.fold (f := fun i a => f i ⊔ a) (by
    intro i j a
    dsimp
    rw [←max_assoc, max_comm (f i), max_assoc]) bot

def max_of_range [Fintype ι] [LE α] [LT α] [Max α] [Bot α] [IsSemiLatticeMax α]
  (f: ι -> α) : α :=
  max_of_range_with f ⊥

def min_of_range_with [Fintype ι] [LE α] [LT α] [Min α] [Top α] [IsSemiLatticeMin α]
  (f: ι -> α) (top: α) : α :=
  max_of_range_with (α := αᵒᵖ) f top

def min_of_range [Fintype ι] [LE α] [LT α] [Min α] [Top α] [IsSemiLatticeMin α]
  (f: ι -> α) : α :=
  min_of_range_with f ⊤

section

variable [Fintype ι] [Fintype ι'] [LE α] [LT α] [Max α] [Min α] [Bot α] [Top α] [IsSemiLatticeMax α] [IsSemiLatticeMin α]
  [IsLawfulBot α] [IsLawfulTop α]

def max_of_range_with_reindex (bij: ι' ↭ ι) (f: ι -> α) : max_of_range_with f bot = max_of_range_with (f ∘ bij) bot := by
  apply Fintype.fold_bij

def max_of_range_reindex (bij: ι' ↭ ι) (f: ι -> α) : max_of_range f = max_of_range (f ∘ bij) := by
  apply max_of_range_with_reindex

def min_of_range_with_reindex (bij: ι' ↭ ι) (f: ι -> α) : min_of_range_with f bot = min_of_range_with (f ∘ bij) bot := by
  apply max_of_range_with_reindex (α := αᵒᵖ)

def min_of_range_reindex (bij: ι' ↭ ι) (f: ι -> α) : min_of_range f = min_of_range (f ∘ bij) :=
  max_of_range_reindex (α := αᵒᵖ) _ _

@[simp] def max_of_range_with_fin_zero (f: Fin 0 -> α) (bot: α) : max_of_range_with f bot = bot := rfl
@[simp] def max_of_range_with_fin_succ (f: Fin (n + 1) -> α) (bot: α) : max_of_range_with f bot = f 0 ⊔ max_of_range_with (f ∘ Fin.succ) bot := by
  apply Fintype.fold_succ

@[simp] def max_of_range_fin_zero (f: Fin 0 -> α) : max_of_range f = ⊥ := rfl
@[simp] def max_of_range_fin_succ (f: Fin (n + 1) -> α) : max_of_range f = f 0 ⊔ max_of_range (f ∘ Fin.succ) := by
  apply max_of_range_with_fin_succ

@[simp] def min_of_range_with_fin_zero (f: Fin 0 -> α) (top: α) : min_of_range_with f top = top := rfl
@[simp] def min_of_range_with_fin_succ (f: Fin (n + 1) -> α) (top: α) : min_of_range_with f top = f 0 ⊓ min_of_range_with (f ∘ Fin.succ) top :=
  max_of_range_with_fin_succ (α := αᵒᵖ) _ _

@[simp] def min_of_range_fin_zero (f: Fin 0 -> α) : min_of_range f = ⊤ := rfl
@[simp] def min_of_range_fin_succ (f: Fin (n + 1) -> α) : min_of_range f = f 0 ⊓ min_of_range (f ∘ Fin.succ) :=
  max_of_range_fin_succ (α := αᵒᵖ) _

end

variable [Fintype ι] [Fintype ι'] [LE α] [LT α] [Max α] [Bot α] [Top α] [IsSemiLatticeMax α]
  [IsLawfulBot α] [IsLawfulTop α]

private def le_max_of_range_with' (i: Fin n) (f: Fin n -> α) (bot: α) : f i ≤ max_of_range_with f bot := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [max_of_range_with_fin_succ]
    cases i using Fin.cases
    apply left_le_max
    apply le_trans _ right_le_max
    apply ih _ (f ∘ Fin.succ)

private def bot_le_max_of_range_with' (f: Fin n -> α) (bot: α) : bot ≤ max_of_range_with f bot := by
  induction n with
  | zero => apply le_refl
  | succ n ih =>
    rw [max_of_range_with_fin_succ]
    apply le_trans _ right_le_max
    apply ih

def le_max_of_range_with (i: ι) (f: ι -> α) (bot: α) : f i ≤ max_of_range_with f bot := by
  induction Fintype.finBij ι with | mk e =>
  rw [max_of_range_with_reindex e]
  obtain ⟨i, rfl⟩ := e.surj i
  apply le_max_of_range_with' _ (f ∘ e)

def bot_le_max_of_range_with (f: ι -> α) (bot: α) : bot ≤ max_of_range_with f bot := by
  induction Fintype.finBij ι with | mk e =>
  rw [max_of_range_with_reindex e]
  apply bot_le_max_of_range_with'

def le_max_of_range (i: ι) (f: ι -> α) : f i ≤ max_of_range f := by
  induction Fintype.finBij ι with | mk e =>
  rw [max_of_range_reindex e]
  obtain ⟨i, rfl⟩ := e.surj i
  apply le_max_of_range_with' _ (f ∘ e)
