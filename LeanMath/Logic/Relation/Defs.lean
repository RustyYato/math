namespace Relation

inductive ReflGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflGen R a a
| of (a b: α) : R a b -> ReflGen R a b

inductive ReflTransGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflTransGen R a a
| cons (a b c: α) : R a b -> ReflTransGen R b c -> ReflTransGen R a c

def ReflTransGen.trans : ReflTransGen R a b -> ReflTransGen R b c -> ReflTransGen R a c := by
  intro h g
  induction h generalizing c with
  | refl => assumption
  | cons _ _ _ _ _ ih =>
    apply ReflTransGen.cons
    assumption
    apply ih
    assumption

def ReflTransGen.of : R a b -> ReflTransGen R a b := by
  intro h; apply ReflTransGen.cons
  assumption
  apply ReflTransGen.refl

private inductive RevReflTransGen (R: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : RevReflTransGen R a a
| snoc (a b c: α) : RevReflTransGen R a b -> R b c -> RevReflTransGen R a c

private def RevReflTransGen.trans : RevReflTransGen R a b -> RevReflTransGen R b c -> RevReflTransGen R a c := by
  intro h g
  induction g generalizing a with
  | refl => assumption
  | snoc _ _ _ h ih =>
    apply RevReflTransGen.snoc
    apply ih
    assumption
    assumption

private def ReflTransGen.rev (h: ReflTransGen R a b) : RevReflTransGen R a b := by
  induction h with
  | refl => apply RevReflTransGen.refl
  | cons a b c h g ih =>
    apply RevReflTransGen.trans
    apply RevReflTransGen.snoc
    apply RevReflTransGen.refl
    assumption
    assumption

private def RevReflTransGen.rev (h: RevReflTransGen R a b) : ReflTransGen R a b := by
  induction h with
  | refl => apply ReflTransGen.refl
  | snoc b c h g ih =>
    apply ReflTransGen.trans
    assumption
    apply ReflTransGen.cons
    assumption
    apply ReflTransGen.refl

def Join (r : α → α → Prop) : α → α → Prop := fun a b ↦ ∃ c, r a c ∧ r b c

-- taken from https://github.com/leanprover-community/mathlib4/blob/6ec9d9723e0d1a046233bd4dfdbf1a11bca1c8dd/Mathlib/Logic/Relation.lean#L771
def church_rosser (h: ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d)
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : Join (ReflTransGen r) b c := by
  replace hab := hab.rev
  replace hac := hac.rev
  induction hab with
  | refl => exact ⟨c, hac.rev, .refl _⟩
  | snoc d e _ hde ih =>
    rcases ih with ⟨b, hdb, hcb⟩
    replace hdb := hdb.rev
    have : ∃ a, ReflTransGen r e a ∧ ReflGen r b a := by
      clear hcb
      induction hdb with
      | refl => exact ⟨e, .refl _, ReflGen.of _ _ hde⟩
      | snoc f b _ hfb ih =>
        rcases ih with ⟨a, hea, hfa⟩
        replace hfa := hfa
        cases hfa with
        | refl => exact ⟨b, (hea.rev.snoc _ _ _ hfb).rev, ReflGen.refl _⟩
        | of _ hfa =>
          rcases h _ _ _ hfb hfa with ⟨c, hbc, hac⟩
          exact ⟨c, hea.trans hac, hbc⟩
    rcases this with ⟨a, hea, hba⟩
    cases hba with
    | refl => exact ⟨b, hea, hcb⟩
    | of _ hba => exact ⟨a, hea, (hcb.rev.snoc _ _ _ hba).rev⟩

end Relation
