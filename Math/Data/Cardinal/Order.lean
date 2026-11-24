module

public import Math.Data.Equiv.Basic
public import Math.Data.Embedding.Basic
public import Math.Data.Cardinal.Defs
public import Math.Order.Defs

namespace Math.Cardinal

public def le : Cardinal -> Cardinal -> Prop :=
  lift₂ (fun a b => Nonempty (a ↪ b)) <| by
    intro A B C D h g
    simp; apply Iff.intro
    intro ⟨f⟩; exact ⟨Equiv.congr_embedding h g f⟩
    intro ⟨f⟩; exact ⟨Equiv.congr_embedding h.symm g.symm f⟩

public instance : LE Cardinal where
  le := le
public instance : LT Cardinal where
  lt a b := a ≤ b ∧ ¬b ≤ a

public theorem type_le_type : A ↪ B -> type A ≤ type B := by
  intro f; show le _ _; unfold le
  rw [lift₂_type]
  exact ⟨f⟩
public theorem of_type_le_type : type A ≤ type B -> Nonempty (A ↪ B) := by
  show le _ _ -> _; unfold le
  rw [lift₂_type]
  exact id

public theorem type_le_type_iff : type A ≤ type B ↔ Nonempty (A ↪ B) := by
  apply Iff.intro of_type_le_type
  intro ⟨f⟩; exact type_le_type f

public instance : IsPreorder Cardinal where
  lt_iff_le_and_not_ge := Iff.rfl
  refl a := by
    induction a; apply type_le_type
    exact .id _
  htrans {A B C} h g := by
    induction A with | _ A =>
    induction B with | _ B =>
    induction C with | _ C =>
    replace ⟨h⟩ := of_type_le_type h
    replace ⟨g⟩ := of_type_le_type g
    apply type_le_type
    exact h.trans g

public def fin : ℕ →o Cardinal where
  toFun n := type (Fin n)
  map_rel_iff {n m} := by
    apply Iff.trans _ type_le_type_iff.symm
    apply Iff.intro
    intro h; exact ⟨Embedding.fin h⟩
    intro ⟨h⟩; exact Embedding.of_fin h

public def ulift : Cardinal.{u} →o Cardinal.{max u v} where
  toFun := lift (fun A => type (ULift A)) <| by
    intro A B h; apply sound
    exact Equiv.congr_ulift h
  map_rel_iff {A B} := by
    induction A with | _ A =>
    induction B with | _ B =>
    rw [lift_type, lift_type]
    apply Iff.trans type_le_type_iff
    apply Iff.trans _ type_le_type_iff.symm
    apply Iff.intro
    intro ⟨f⟩; refine ⟨?_⟩
    exact (Equiv.congr_embedding Equiv.ulift Equiv.ulift).symm f
    intro ⟨f⟩; refine ⟨?_⟩
    exact Equiv.congr_embedding Equiv.ulift Equiv.ulift f

public def plift : Cardinal.{u} →o Cardinal.{u + 1} where
  toFun := lift (fun A => type (PLift A)) <| by
    intro A B h; apply sound
    exact Equiv.congr_plift h
  map_rel_iff {A B} := by
    induction A with | _ A =>
    induction B with | _ B =>
    rw [lift_type, lift_type]
    apply Iff.trans type_le_type_iff
    apply Iff.trans _ type_le_type_iff.symm
    apply Iff.intro
    intro ⟨f⟩; refine ⟨?_⟩
    exact (Equiv.congr_embedding Equiv.plift Equiv.plift).symm f
    intro ⟨f⟩; refine ⟨?_⟩
    exact Equiv.congr_embedding Equiv.plift Equiv.plift f
