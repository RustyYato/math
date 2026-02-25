class IsEmpty (α: Sort u) : Prop where
  elim: α -> False

def rec_elim_empty {motive: α -> Sort _} [IsEmpty α] : ∀x, motive x :=
  fun a => nomatch IsEmpty.elim a
def elim_empty [IsEmpty α] : α -> β := rec_elim_empty

instance : IsEmpty False where
  elim := id
instance : IsEmpty Empty where
  elim := nofun
instance : IsEmpty PEmpty where
  elim := nofun
instance [IsEmpty α] : IsEmpty (α ×' β) where
  elim x := elim_empty x.1
instance [IsEmpty β] : IsEmpty (α ×' β) where
  elim x := elim_empty x.2
instance [IsEmpty α] : IsEmpty (α × β) where
  elim x := elim_empty x.1
instance [IsEmpty β] : IsEmpty (α × β) where
  elim x := elim_empty x.2
instance [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) where
  elim
  | .inl x => elim_empty x
  | .inr x => elim_empty x
instance [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) where
  elim
  | .inl x => elim_empty x
  | .inr x => elim_empty x
instance {β: α -> Sort _} [Nonempty α] [∀x, IsEmpty (β x)] : IsEmpty (∀x, β x) where
  elim f := by
    have ⟨x⟩ := inferInstanceAs (Nonempty α)
    exact elim_empty (f x)
instance [Nonempty α] [IsEmpty β] : IsEmpty (α -> β) := inferInstance
instance [IsEmpty α] : Subsingleton α where
  allEq := rec_elim_empty
instance : IsEmpty (Fin 0) where
  elim := Fin.elim0
