module

public class IsEmpty (α: Sort u) : Prop where
  elim: α -> False

public def rec_elim_empty {motive: α -> Sort _} [IsEmpty α] : ∀x, motive x :=
  fun a => nomatch IsEmpty.elim a
public def elim_empty [IsEmpty α] : α -> β := rec_elim_empty

public instance : IsEmpty False where
  elim := id
public instance : IsEmpty Empty where
  elim := nofun
public instance : IsEmpty PEmpty where
  elim := nofun
public instance [IsEmpty α] : IsEmpty (α ×' β) where
  elim x := elim_empty x.1
public instance [IsEmpty β] : IsEmpty (α ×' β) where
  elim x := elim_empty x.2
public instance [IsEmpty α] : IsEmpty (α × β) where
  elim x := elim_empty x.1
public instance [IsEmpty β] : IsEmpty (α × β) where
  elim x := elim_empty x.2
public instance [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕' β) where
  elim
  | .inl x => elim_empty x
  | .inr x => elim_empty x
public instance [IsEmpty α] [IsEmpty β] : IsEmpty (α ⊕ β) where
  elim
  | .inl x => elim_empty x
  | .inr x => elim_empty x
public instance {β: α -> Sort _} [Nonempty α] [∀x, IsEmpty (β x)] : IsEmpty (∀x, β x) where
  elim f := by
    have ⟨x⟩ : Nonempty α := inferInstance
    exact elim_empty (f x)
public instance [Nonempty α] [IsEmpty β] : IsEmpty (α -> β) := inferInstance
public instance [IsEmpty α] : Subsingleton α where
  allEq := rec_elim_empty
public instance : IsEmpty (Fin 0) where
  elim := Fin.elim0
public instance [IsEmpty α] : IsEmpty (ULift α) where
  elim x := elim_empty x.down

public instance [IsEmpty ι] {α: ι -> Sort u} : Subsingleton (∀i, α i) where
  allEq f g := by ext i; exact elim_empty i

public instance [IsEmpty ι] {α: ι -> Sort u} : Inhabited (∀i, α i) where
  default := rec_elim_empty
