module

public class ExcludedMiddle (P: Prop) where
  protected excluded_middle : P ∨ ¬P

public theorem em (P: Prop) [ExcludedMiddle P] : P ∨ ¬ P := ExcludedMiddle.excluded_middle

public abbrev LEM := ∀P, ExcludedMiddle P

public abbrev ExcludedMiddleEq (α: Sort u) := ∀a b: α, ExcludedMiddle (a = b)
public abbrev ExcludedMiddlePred (P: α -> Prop) := ∀a, ExcludedMiddle (P a)

namespace LEM

public theorem or_iff_not_imp_left : ∀ {a b : Prop} [ExcludedMiddle a], a ∨ b ↔ ¬a → b := by
  intro P Q _
  have ⟨h⟩ : Nonempty (Decidable P) := inferInstance
  apply Decidable.or_iff_not_imp_left

public theorem or_iff_not_imp_right : ∀ {a b : Prop} [ExcludedMiddle b], a ∨ b ↔ ¬b → a := by
  intro P Q _
  have ⟨h⟩ : Nonempty (Decidable Q) := inferInstance
  apply Decidable.or_iff_not_imp_right

public theorem byContradiction {P: Prop} [ExcludedMiddle P] : (¬P -> False) -> P := by
  intro hp
  rcases em P with h | h
  exact h
  nomatch hp h

public theorem not_forall [LEM] {P: α -> Prop} : (¬∀a, P a) ↔ ∃a, ¬P a := by
  apply Iff.intro
  intro g; apply byContradiction
  intro h
  apply g; intro a;
  exact byContradiction (fun x => h ⟨a, x⟩)
  intro ⟨a, ha⟩ g
  exact ha (g _)

public theorem not_iff_not : ∀ {a b : Prop} [ExcludedMiddle a] [ExcludedMiddle b], (¬a ↔ ¬b) ↔ (a ↔ b) := by
  intro P Q _ _
  apply Iff.intro <;> (intro h; apply Iff.intro <;> intro g)
  apply byContradiction
  intro g'; exact h.mpr g' g
  apply byContradiction
  intro g'; exact h.mp g' g
  intro g'; exact g (h.mpr g')
  intro g'; exact g (h.mp g')

public theorem not_not [ExcludedMiddle P] : ¬¬P ↔ P := by
  apply Iff.intro
  apply byContradiction
  intro p np
  exact np p

public theorem iff_iff_and_or_not_and_not {a b : Prop} [ExcludedMiddle b] :
    (a ↔ b) ↔ (a ∧ b) ∨ (¬a ∧ ¬b) := by
    apply Iff.intro
    · intro h
      rcases em b with x | x
      left; exact And.intro (h.mpr x) x
      right; apply And.intro _ x
      intro y
      exact x (h.mp y)
    · intro h
      rcases h with ⟨_, _⟩ | ⟨_, _⟩
      apply Iff.intro <;> (intro; assumption)
      apply Iff.intro <;> (intro; contradiction)

public theorem not_and {P Q: Prop} [ExcludedMiddle P] : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  apply Iff.intro
  · intro h
    rcases em P with p | p
    right; intro q
    exact h ⟨p, q⟩
    left; assumption
  · intro h ⟨_, _⟩
    rcases h <;> contradiction

instance (P: Prop) [dec: Decidable P] : ExcludedMiddle P where
  excluded_middle := dec.em

section

variable (P Q: Prop) [ExcludedMiddle P] [ExcludedMiddle Q]

instance [ExcludedMiddle P] : ExcludedMiddle (¬P) where
  excluded_middle := by
    rcases em P with h | h
    right; intro g; exact g h
    left; assumption

instance : ExcludedMiddle (P ∧ Q) where
  excluded_middle := by
    rcases em P with p | np
    rcases em Q with q | nq
    left; constructor <;> assumption
    iterate 2
    right; intro ⟨_, _⟩; contradiction

instance : ExcludedMiddle (P ∨ Q) where
  excluded_middle := by
    rcases em P with p | np
    left; left; assumption
    rcases em Q with q | nq
    left; right; assumption
    right; intro h; cases h <;> contradiction

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

instance (priority := 500) {P: α -> Prop} [ExcludedMiddlePred P] [ExcludedMiddle (∃a, ¬P a)] : ExcludedMiddle (∀a, P a) where
  excluded_middle := by
    rcases em (∃a, ¬P a) with ⟨a, pa⟩ | h
    · right; intro h; exact pa (h _)
    · left; intro a
      exact LEM.not_not.mp (h ⟨a, ·⟩)

end

end LEM

namespace Classical

public scoped instance : ExcludedMiddle P where
  excluded_middle := Classical.em P

end Classical
