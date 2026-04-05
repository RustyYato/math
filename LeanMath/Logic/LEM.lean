class ExcludedMiddle (P: Prop) where
  em : P ∨ ¬P

abbrev ExcludedMiddleEq (α: Sort u) := ∀a b: α, ExcludedMiddle (a = b)
abbrev ExcludedMiddlePred (P: α -> Prop) := ∀a, ExcludedMiddle (P a)

scoped instance Classical.ExcludedMiddle : ExcludedMiddle P where
  em := Classical.em _

-- any theories which are non-constructive will have this as a precondition
-- or use Classical as an axiom
abbrev LEM := ∀P, ExcludedMiddle P

instance [Decidable P] : ExcludedMiddle P where
  em := Decidable.em _

def em (P: Prop) [ExcludedMiddle P] : P ∨ ¬P := ExcludedMiddle.em

instance (priority := 10000) instNonemptyDecidableOfEM (P: Prop) [ExcludedMiddle P] : Nonempty (Decidable P) := by
  rcases em P with h | h
  exact .intro (.isTrue h)
  exact .intro (.isFalse h)

namespace LEM

def byCases
  {P Q: Prop}
  [ExcludedMiddle P]
  (ofTrue: P -> Q)
  (ofFalse: ¬P -> Q) : Q := by
  rcases em P with h | h
  exact ofTrue h
  exact ofFalse h

def or_iff_not_imp_left : ∀ {a b : Prop} [ExcludedMiddle a], a ∨ b ↔ ¬a → b := by
  intro P Q _
  have ⟨h⟩ : Nonempty (Decidable P) := inferInstance
  apply Decidable.or_iff_not_imp_left

def or_iff_not_imp_right : ∀ {a b : Prop} [ExcludedMiddle b], a ∨ b ↔ ¬b → a := by
  intro P Q _
  have ⟨h⟩ : Nonempty (Decidable Q) := inferInstance
  apply Decidable.or_iff_not_imp_right

def byContradiction {P: Prop} [ExcludedMiddle P] : (¬P -> False) -> P := by
  intro hp
  rcases em P with h | h
  exact h
  nomatch hp h

def not_forall [LEM] {P: α -> Prop} : (¬∀a, P a) ↔ ∃a, ¬P a := by
  apply Iff.intro
  intro g; apply byContradiction
  intro h
  apply g; intro a;
  exact byContradiction (fun x => h ⟨a, x⟩)
  intro ⟨a, ha⟩ g
  exact ha (g _)

instance [ExcludedMiddle P] : ExcludedMiddle (¬P) where
  em := by
    rcases em P with h | h
    right; intro g; exact g h
    left; assumption

def not_iff_not : ∀ {a b : Prop} [ExcludedMiddle a] [ExcludedMiddle b], (¬a ↔ ¬b) ↔ (a ↔ b) := by
  intro P Q _ _
  apply Iff.intro <;> (intro h; apply Iff.intro <;> intro g)
  apply byContradiction
  intro g'; exact h.mpr g' g
  apply byContradiction
  intro g'; exact h.mp g' g
  intro g'; exact g (h.mpr g')
  intro g'; exact g (h.mp g')

def not_not [ExcludedMiddle P] : ¬¬P ↔ P := by
  apply Iff.intro
  apply byContradiction
  intro p np
  exact np p

end LEM

instance {α: Type u} (x: α) [∀b: α, ExcludedMiddle (x = b)] (as: List α) : ExcludedMiddle (x ∈ as) := by
  induction as with
  | nil =>
    apply ExcludedMiddle.mk
    right; nofun
  | cons a as =>
    apply ExcludedMiddle.mk
    rcases em (x = a) with ha | ha
    · left; rw [ha]; apply List.Mem.head
    rcases em (x ∈ as) with h | h
    · left; apply List.Mem.tail; assumption
    · right; intro g
      cases g <;> contradiction

def existsUnique (P: α -> Prop) := ∃a, P a ∧ ∀b, P b -> a = b

-- noncomputable def Classical.unique_choice {α: Sort u} (h: Nonempty α) [Subsingleton α] : α := Classical.choice h
axiom Classical.unique_choice {α: Sort u} (h: Nonempty α) [Subsingleton α] : α

noncomputable instance (priority := 10) [Nonempty α] [Subsingleton α] : Inhabited α where
  default := Classical.unique_choice inferInstance

noncomputable scoped instance (priority := 2) UniqueChoice.instDecidable [ExcludedMiddle P] : Decidable P := default

private noncomputable def Classical.choose_unique_aux {P: α -> Prop} (h: existsUnique P) : Σ'a, P a :=
    have : Subsingleton (Σ'a, P a) := {
      allEq := by
        intro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨x, hx, g⟩ := h
        cases g _ ha
        cases g _ hb
        rfl
    }
    Classical.unique_choice (by
      obtain ⟨a, ha, _⟩ := h
      exists a)
noncomputable def Classical.choose_unique {P: α -> Prop} (h: existsUnique P) : α :=
  (Classical.choose_unique_aux h).fst
def Classical.choose_unique_spec {P: α -> Prop} (h: existsUnique P) : P (choose_unique h) :=
  (Classical.choose_unique_aux h).snd
def Classical.choose_unique_spec_unique {P: α -> Prop} (h: existsUnique P) : ∀x, P x -> choose_unique h = x := by
  obtain ⟨x, hx, g⟩ := h; intro y hy
  rw [←g _ hy]
  symm; apply g
  apply choose_unique_spec

def Classical.axiomOfUniqueChoice {α: Sort u} {β: α -> Sort v} {P: ∀a: α, β a -> Prop} (h: ∀a, existsUnique (P a)) : ∃f: ∀a, β a, ∀a, P a (f a) ∧ ∀g: (∀a, β a), (∀a, P a (g a)) -> ∀a, f a = g a := by
  exists fun a => Classical.choose_unique (h a)
  intro a
  apply And.intro
  apply Classical.choose_unique_spec
  intro g hg a
  apply Classical.choose_unique_spec_unique
  apply hg

instance {P: Fin n -> Prop} [ExcludedMiddlePred P] : ExcludedMiddle (∃a, P a) where
  em := by
    induction n with
    | zero => right; nofun
    | succ n ih =>
      rcases em (P ⟨0, Nat.zero_lt_succ _⟩) with h₀ | h₀
      exact .inl ⟨_, h₀⟩
      rcases ih (P := fun i => P i.succ) with h₁ | h₁
      obtain ⟨a, pa⟩ := h₁
      exact .inl ⟨_, pa⟩
      right; intro ⟨a, ha⟩
      match a with
      | ⟨0, _⟩ => contradiction
      | ⟨a + 1, h⟩ =>
        apply h₁
        exact ⟨⟨a, Nat.lt_of_succ_lt_succ h⟩, ha⟩

instance (priority := 500) {P: α -> Prop} [ExcludedMiddlePred P] [ExcludedMiddle (∃a, ¬P a)] : ExcludedMiddle (∀a, P a) where
  em := by
    rcases em (∃a, ¬P a) with ⟨a, pa⟩ | h
    · right; intro h; exact pa (h _)
    · left; intro a
      exact LEM.not_not.mp (h ⟨a, ·⟩)
