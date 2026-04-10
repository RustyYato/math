import LeanMath.Order.Defs

def List.min_append [Min α] [LE α] [LT α] [IsSemiLatticeMin α] (as bs: List α) (ha: as ≠ []) (hb: bs ≠ []) :
  (as ++ bs).min (by
    intro h
    have ⟨_, _⟩ := List.append_eq_nil_iff.mp h
    contradiction) = (as.min ha) ⊓ (bs.min hb) := by
  cases as with
  | nil => contradiction
  | cons a as =>
  cases bs with
  | nil => contradiction
  | cons b bs =>
  unfold List.min; dsimp
  clear ha hb
  induction as generalizing a b bs with
  | nil =>
    dsimp
    induction bs generalizing a b with
    | nil => dsimp
    | cons a' as ih =>
      rw [List.foldl_cons, List.foldl_cons]
      rw [ih, ih, ←min_assoc]
  | cons a' as ih =>
    rw [List.cons_append, List.foldl_cons, List.foldl_cons]
    rw [ih]

def List.min_cons' [Min α] [LE α] [LT α] [IsSemiLatticeMin α] (x a) (as: List α) : List.min (x::a::as) nofun = x ⊓ List.min (a::as) nofun := by
  unfold List.min; dsimp
  induction as generalizing a x with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, min_assoc x, List.foldl_cons, ih]

def List.min_cons'' [Min α] [LE α] [LT α] [IsSemiLatticeMin α] (x) (as: List α) (has: as ≠ []) : List.min (x::as) nofun = x ⊓ List.min as has := by
  cases as; contradiction
  apply List.min_cons'

def List.min_le_of_mem' [Min α] [LE α] [LT α] [IsSemiLatticeMin α] (x) (as: List α) (h: x ∈ as) : List.min as (by intro rfl; contradiction) ≤ x := by
  unfold List.min; dsimp
  cases as with
  | nil => contradiction
  | cons a as =>
  dsimp
  have le_acc : ∀(x: α) (as: List α), foldl min x as ≤ x := by
    clear h a x as; intro x as
    induction as generalizing x with
    | nil => rfl
    | cons a as ih =>
      dsimp; apply le_trans
      apply ih
      apply min_le_left
  rcases h with _ | ⟨_, h⟩
  apply le_acc
  induction as generalizing x a with
  | nil => contradiction
  | cons a' as ih =>
    dsimp
    cases h
    apply le_trans; apply le_acc; apply min_le_right
    apply ih
    assumption

def List.min_eq_foldr [Min α] [LE α] [LT α] [IsSemiLatticeMin α] (a: α) (as: List α) : List.min (a::as) nofun = List.foldr (· ⊓ ·) a as := by
  unfold List.min; dsimp
  induction as generalizing a with
  | nil => rfl
  | cons a' as ih =>
    rw [List.foldl_cons, List.foldr_cons, ih]
    clear ih
    induction as generalizing a a' with
    | nil => dsimp; rw [min_comm]
    | cons a'' as ih => dsimp; rw [←min_assoc, min_comm a', min_assoc, ih]

def List.min_eq_of_perm [Min α] [LE α] [LT α] [IsSemiLatticeMin α] (as bs: List α) (h: as.Perm bs) (ha: as ≠ []) : List.min as ha = List.min bs (by
  intro rfl
  exact ha (List.perm_nil.mp h)) := by
  induction h with
  | nil => contradiction
  | @cons a as bs perm ih =>
    rcases em (as = []) with ha | ha
    subst ha; cases (List.nil_perm.mp perm)
    rfl
    have hb : bs ≠ [] := by
      intro rfl; apply ha
      exact (List.perm_nil.mp perm)
    rw [List.min_cons'' _ _ ha, List.min_cons'' _ _ hb, ih]
  | @trans as bs cs has hbs iha ihb => rw [iha, ihb]
  | swap a b xs =>
    unfold List.min; dsimp
    rw [min_comm]
