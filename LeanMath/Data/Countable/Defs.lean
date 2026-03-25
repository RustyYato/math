import LeanMath.Data.Encodable.Defs

abbrev IsCountable (α: Sort*) : Prop := Nonempty (Encodable α)

instance {α: Sort*} [Encodable α] : IsCountable α := ⟨inferInstance⟩

private def cantor_diag_func [Encodable (ℕ -> Bool)] : ℕ -> Bool :=
  fun n => match Encodable.decode (α := ℕ -> Bool) n with
    | .none => false
    | .some f => !(f n)

def cantor_diag (h: IsCountable (ℕ -> Bool)) : False := by
  obtain ⟨h⟩ := h
  let x := Encoding.mk cantor_diag_func
  suffices cantor_diag_func x.encoding ≠ cantor_diag_func x.encoding by contradiction
  rw (occs := [1]) [cantor_diag_func]
  rw [Encoding.decode_encoding]
  dsimp
  simp [x]; symm
  rw [Encoding.mk_val]

def IsCountable.axiomOfChoice {α: Type*} {β: Type*} [hc: IsCountable β] {P: α -> β -> Prop} [∀a, DecidablePred (P a)] (h: ∀a, ∃b: β, P a b) : ∃f: α -> β, ∀a, P a (f a) := by
  obtain ⟨⟩ := hc
  refine ⟨fun a => Encodable.choice (h a) ,?_⟩
  intro a
  apply Encodable.choice_spec
