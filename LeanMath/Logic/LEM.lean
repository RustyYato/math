class ExcludedMiddle (P: Prop) where
  em : P ∨ ¬P

abbrev ExcludedMiddleEq (α: Sort u) := ∀a b: α, ExcludedMiddle (a = b)

scoped instance Classical.ExcludedMiddle : ExcludedMiddle P where
  em := Classical.em _

-- any theories which are non-constructive will have this as a precondition
-- or use Classical as an axiom
abbrev LEM := ∀P, ExcludedMiddle P

instance [Decidable P] : ExcludedMiddle P where
  em := Decidable.em _

def em (P: Prop) [ExcludedMiddle P] : P ∨ ¬P := ExcludedMiddle.em

instance (priority := 10000) [ExcludedMiddle P] : Nonempty (Decidable P) := by
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
  have ⟨_⟩ := inferInstanceAs (Nonempty (Decidable P))
  apply Decidable.or_iff_not_imp_left

def or_iff_not_imp_right : ∀ {a b : Prop} [ExcludedMiddle b], a ∨ b ↔ ¬b → a := by
  intro P Q _
  have ⟨_⟩ := inferInstanceAs (Nonempty (Decidable Q))
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
