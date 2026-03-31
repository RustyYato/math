import LeanMath.Data.Fintype.Defs
import LeanMath.Data.Fintype.Pairing
import LeanMath.Data.Fintype.Pi
import LeanMath.Data.Set.Relation

namespace Set

variable [LEM] (s t: Set α)

def finite_of_sub {s t: Set α} (h: t ⊆ s) [Finite s] : Finite t := by
  apply Finite.ofEmbed (β := s)
  exact {
    toFun x := {
      val := x.val
      property := h _ x.property
    }
    inj := by
      intro ⟨_, _⟩ ⟨_, _⟩ h
      cases h; rfl
  }

instance [Finite s] : Finite (s.sep P: Set α) := by
  apply finite_of_sub (s := s)
  intro x; exact And.left
instance [Finite s] : Finite (s ∩ t: Set α) := inferInstanceAs (Finite (s.sep _))
instance [Finite t] : Finite (s ∩ t: Set α) := by
  rw [inter_comm]
  infer_instance
instance [Finite s] : Finite (s \ t: Set α) := inferInstanceAs (Finite (s.sep _))
instance [Finite s] [Finite t] : Finite (s ∪ t: Set α) := by
  apply Finite.ofEmbed (β := s ⊕ t)
  open UniqueChoice in
  exact {
    toFun x :=
      if hx:x.val ∈ s then
        .inl ⟨x.val, hx⟩
      else
        .inr ⟨x.val, by
          cases x.property
          contradiction
          assumption⟩
    inj := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ h
      dsimp at h
      split at h <;> split at h
      cases Sum.inl.inj h; rfl
      nomatch h
      nomatch h
      cases Sum.inr.inj h; rfl
  }
instance [Finite s] : Finite (s.powerset: Set (Set α)) := by
  open UniqueChoice in
  apply Finite.ofEmbed (β := s -> Prop)
  exact {
    toFun U x := x.val ∈ U.val
    inj := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ h
      dsimp at h
      replace h := fun x => congrFun h x
      ext x
      dsimp
      apply Iff.intro
      intro hx
      have := h ⟨_, ha _ hx⟩
      dsimp at this
      rwa [←this]
      intro hx
      have := h ⟨_, hb _ hx⟩
      dsimp at this
      rwa [this]
  }

instance [Finite α] : Finite s := by
  apply Finite.ofEmbed (β := α)
  apply Embedding.subtype_val

def finite_induction
  (motive: Set α -> Prop)
  (nil: motive ⊥)
  (cons: ∀x xs, motive xs -> motive (insert x xs))
  (s: Set α) [hf: Finite s] : motive s := by
  obtain ⟨card, hf⟩ := hf
  induction hf with | _ hf =>
  obtain ⟨hf, x⟩ := hf; clear x
  induction card generalizing s with
  | zero =>
    rw [show s = ⊥ from ?_]
    apply nil
    ext x; simp
    intro hx
    nomatch hf.surj ⟨_, hx⟩
  | succ n ih =>
    let a := hf 0
    rw [show s = insert a.val (s \ {a.val}) from ?_]
    apply cons
    apply ih
    · simp
      refine {
        toFun x := {
          val := hf x.succ
          property := ?_
        }
        inj' := ?_
        surj' := ?_
      }
      · apply And.intro
        apply Subtype.property
        intro g
        exact Fin.succ_ne_zero _ (hf.inj (Subtype.val_inj g)).symm
      · intro a b h
        dsimp at h
        exact Fin.succ_inj.mp <| hf.inj (Subtype.val_inj (Subtype.mk.inj h))
      · intro ⟨x, hx, ne⟩
        have ⟨i, hi⟩ := hf.surj ⟨x, hx⟩
        cases i using Fin.cases with
        | zero =>
          have : a = _ := hi
          rw [this] at ne
          contradiction
        | succ i =>
          exists i
          dsimp
          congr
          apply congrArg Subtype.val hi
    · ext i
      rcases em (a.val = i) with h | h
      simp [h]
      rw [←h]
      apply a.property
      simp [h]
      intro rfl; contradiction

instance (r: α -> α -> Prop) [Finite s] [Relation.IsTrans r] [Relation.IsIrrefl r] : Relation.IsWelFounded (s.Induced r) where
  wf := by
    induction s using finite_induction with
    | nil =>
      apply WellFounded.intro
      nofun
    | cons x xs ih =>
      apply WellFounded.intro
      intro ⟨a, ha⟩
      simp at ha
      have insert_self (a: α) : Acc (Induced r (insert a xs)) ⟨a, by simp⟩ := by
        apply Acc.intro
        intro ⟨b, hb⟩ h
        have : b ∈ xs := by
          rcases hb with rfl | hb
          nomatch Relation.irrefl (R := r) h
          assumption
        show Acc ((insert a xs).Induced r) ⟨b, Set.mem_insert.mpr (.inr this)⟩
        replace h: r b a := h
        clear hb; revert h
        induction h:(Subtype.mk b this) using ih.induction generalizing b with
        | h b ih =>
        subst h
        intro h
        simp only [Subtype.forall, Subtype.mk.injEq, Set.Induced] at ih
        replace ih (x: α) (hx: x ∈ xs) : r x b -> Acc ((insert a xs).Induced r) ⟨x, by simp [hx]⟩ := by
          intro rxb
          exact ih x hx rxb x hx rfl (Relation.trans rxb h)
        apply Acc.intro
        intro ⟨x, hx⟩ g
        rcases hx with rfl | hx
        nomatch Relation.asymm h g
        exact ih x hx g
      rcases ha with rfl | ha
      · apply insert_self
      · show Acc ((insert x xs).Induced r) ⟨a, Set.mem_insert.mpr (.inr ha)⟩
        induction h:(Subtype.mk a ha) using ih.induction generalizing a with
        | h a ih =>
          subst h
          apply Acc.intro
          intro ⟨b, hb⟩ h
          rcases hb with rfl | hb
          replace h : r _ _ := h
          apply insert_self
          apply ih ⟨b, hb⟩
          exact h
          simp [hb]
          rfl

def eqv_induced_univ (r: α -> α -> Prop) : r ≃r (⊤: Set α).Induced r where
  toFun x := ⟨x, True.intro⟩
  invFun x := x.val
  leftInv _ := rfl
  rightInv _ := rfl
  map_rel := Iff.rfl

end Set

instance [LEM] {α: Type u} [Finite α] (r: α -> α -> Prop) [Relation.IsTrans r] [Relation.IsIrrefl r] : Relation.IsWelFounded r :=
  (Set.eqv_induced_univ r).liftWellfounded
