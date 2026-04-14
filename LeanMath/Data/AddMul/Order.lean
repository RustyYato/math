import LeanMath.Data.AddMul.Defs
import LeanMath.Order.Defs

variable [LE α] [LT α] [Min α] [Max α]

section

attribute [local irreducible] AddOfMul MulOfAdd

instance : LE (AddOfMul α) where
  le a b := a.get ≤ b.get
instance : LE (MulOfAdd α) where
  le a b := a.get ≤ b.get
instance : LE (MulOpp α) where
  le a b := a.get ≤ b.get
instance : LE (AddOpp α) where
  le a b := a.get ≤ b.get
instance : LT (AddOfMul α) where
  lt a b := a.get < b.get
instance : LT (MulOfAdd α) where
  lt a b := a.get < b.get
instance : LT (MulOpp α) where
  lt a b := a.get < b.get
instance : LT (AddOpp α) where
  lt a b := a.get < b.get
instance : Min (AddOfMul α) where
  min a b := .mk <| a.get ⊓ b.get
instance : Min (MulOfAdd α) where
  min a b := .mk <| a.get ⊓ b.get
instance : Min (MulOpp α) where
  min a b := .mk <| a.get ⊓ b.get
instance : Min (AddOpp α) where
  min a b := .mk <| a.get ⊓ b.get
instance : Max (AddOfMul α) where
  max a b := .mk <| a.get ⊔ b.get
instance : Max (MulOfAdd α) where
  max a b := .mk <| a.get ⊔ b.get
instance : Max (MulOpp α) where
  max a b := .mk <| a.get ⊔ b.get
instance : Max (AddOpp α) where
  max a b := .mk <| a.get ⊔ b.get

end

instance [IsLawfulLT α] : IsLawfulLT (AddOfMul α) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := α)
instance [IsLawfulLT α] : IsLawfulLT (MulOfAdd α) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := α)
instance [IsLawfulLT α] : IsLawfulLT (MulOpp α) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := α)
instance [IsLawfulLT α] : IsLawfulLT (AddOpp α) where
  lt_iff_le_and_not_ge := lt_iff_le_and_not_ge (α := α)
instance [IsPreorder α] : IsPreorder (AddOfMul α) where
  refl _ := le_refl (α := α) _
  trans := le_trans (α := α)
instance [IsPreorder α] : IsPreorder (MulOfAdd α) where
  refl _ := le_refl (α := α) _
  trans := le_trans (α := α)
instance [IsPreorder α] : IsPreorder (MulOpp α) where
  refl _ := le_refl (α := α) _
  trans := le_trans (α := α)
instance [IsPreorder α] : IsPreorder (AddOpp α) where
  refl _ := le_refl (α := α) _
  trans := le_trans (α := α)
instance [IsPartialOrder α] : IsPartialOrder (AddOfMul α) where
  antisymm := le_antisymm (α := α)
instance [IsPartialOrder α] : IsPartialOrder (MulOfAdd α) where
  antisymm := le_antisymm (α := α)
instance [IsPartialOrder α] : IsPartialOrder (MulOpp α) where
  antisymm := le_antisymm (α := α)
instance [IsPartialOrder α] : IsPartialOrder (AddOpp α) where
  antisymm := le_antisymm (α := α)
instance [IsLinearOrder α] : IsLinearOrder (AddOfMul α) where
  connected := lt_trichotomy (α := α)
instance [IsLinearOrder α] : IsLinearOrder (MulOfAdd α) where
  connected := lt_trichotomy (α := α)
instance [IsLinearOrder α] : IsLinearOrder (MulOpp α) where
  connected := lt_trichotomy (α := α)
instance [IsLinearOrder α] : IsLinearOrder (AddOpp α) where
  connected := lt_trichotomy (α := α)
instance [IsSemiLatticeMax α] : IsSemiLatticeMax (AddOfMul α) where
  left_le_max := left_le_max (α := α)
  right_le_max := right_le_max (α := α)
  max_le := max_le (α := α)
instance [IsSemiLatticeMax α] : IsSemiLatticeMax (MulOfAdd α) where
  left_le_max := left_le_max (α := α)
  right_le_max := right_le_max (α := α)
  max_le := max_le (α := α)
instance [IsSemiLatticeMax α] : IsSemiLatticeMax (MulOpp α) where
  left_le_max := left_le_max (α := α)
  right_le_max := right_le_max (α := α)
  max_le := max_le (α := α)
instance [IsSemiLatticeMax α] : IsSemiLatticeMax (AddOpp α) where
  left_le_max := left_le_max (α := α)
  right_le_max := right_le_max (α := α)
  max_le := max_le (α := α)
instance [IsSemiLatticeMin α] : IsSemiLatticeMin (AddOfMul α) where
  min_le_left := min_le_left (α := α)
  min_le_right := min_le_right (α := α)
  le_min := le_min (α := α)
instance [IsSemiLatticeMin α] : IsSemiLatticeMin (MulOfAdd α) where
  min_le_left := min_le_left (α := α)
  min_le_right := min_le_right (α := α)
  le_min := le_min (α := α)
instance [IsSemiLatticeMin α] : IsSemiLatticeMin (MulOpp α) where
  min_le_left := min_le_left (α := α)
  min_le_right := min_le_right (α := α)
  le_min := le_min (α := α)
instance [IsSemiLatticeMin α] : IsSemiLatticeMin (AddOpp α) where
  min_le_left := min_le_left (α := α)
  min_le_right := min_le_right (α := α)
  le_min := le_min (α := α)
instance [IsLattice α] : IsLattice (AddOfMul α) where
instance [IsLattice α] : IsLattice (MulOfAdd α) where
instance [IsLattice α] : IsLattice (MulOpp α) where
instance [IsLattice α] : IsLattice (AddOpp α) where
