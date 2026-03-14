import LeanMath.Order.CompleteLattice

instance : LE (Set α) where
  le a b := a ⊆ b
instance : LT (Set α) where
  lt a b := a ≤ b ∧ ¬b ≤ a
instance : Min (Set α) where
  min a b := a ∩ b
instance : Max (Set α) where
  max a b := a ∪ b

instance : IsCompleteLattice (Set α) where
  lt_iff_le_and_not_ge := Iff.rfl
  refl := Set.sub_refl
  trans := Set.sub_trans
  antisymm := Set.sub_antisymm
  min_le_left _ := And.left
  min_le_right _ := And.right
  le_min ha hb x hx := ⟨ha x hx, hb x hx⟩
  left_le_max _ := Or.inl
  right_le_max _ := Or.inr
  max_le ha hb x hx :=
    match hx with
    | .inl hx => ha x hx
    | .inr hx => hb x hx
  sInf_le U u hu x hx := hx u hu
  le_sInf U u h x hx v hv := h v hv x hx
  sSup_le := by
    rintro U x h a ⟨s, hs, ha⟩
    apply h
    assumption
    assumption
  le_sSup := by
    rintro U u hu x hx
    exists u
  le_top := Set.sub_top
  bot_le := Set.bot_sub
