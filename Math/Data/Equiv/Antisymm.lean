module

public import Math.Data.Bijection.Defs
public import Math.Data.Embedding.Defs
public import Math.Data.Equiv.Defs

import Math.Logic.UniqueChoice
import Math.Tactic.Basic
import Math.Data.Set.Basic
import Math.Order.Set

namespace Math

open Classical.UniqueChoice

noncomputable def inv [LEM] (f: α ↪ β) (b: β) : Option α :=
  if h:b ∈ Set.range f then
    .some <| Classical.unique_choose <| by
      change exists_unique fun a => f a = b
      simp at h; obtain ⟨a, ha⟩ := h
      refine ⟨_, ha, ?_⟩
      intro a' ha'
      apply f.inj
      rw [ha, ha']
  else
    .none

theorem inv_left [LEM] (f: α ↪ β) (a: α) : inv f (f a) = a := by
  unfold inv
  have : f a ∈ Set.range f := Set.mem_range'
  rw [dite_eq_left this]; congr; apply f.inj
  apply Classical.unique_choose_spec (P := fun a' => f a' = f a)

theorem inv_right [LEM] (f: α ↪ β) (b: β) (hb: b ∈ Set.range f) : (inv f b).map f = b := by
  unfold inv; rw [dite_eq_left hb]
  dsimp; congr 1;
  apply Classical.unique_choose_spec (P := fun a' => f a' = b)

def image_chain
  (f: α ↪ β) (g: β ↪ α) : ℕ -> Set α
| 0 => Set.range g
| n + 1 =>
  let S := image_chain f g n
  (S.image f).image g

theorem image_chain_sub_succ (f: α ↪ β) (g: β ↪ α) (n: ℕ) : image_chain f g (n + 1) ⊆ image_chain f g n := by
  dsimp [image_chain]
  intro a; simp
  intro a ha' rfl
  induction n generalizing a with
  | zero =>
    unfold image_chain
    apply Set.mem_range'
  | succ n ih =>
    dsimp [image_chain] at *
    simp at ha'
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := ha'
    apply Set.mem_image'
    apply Set.mem_image'
    apply ih
    assumption

theorem image_chain_sub (f: α ↪ β) (g: β ↪ α) :
  ∀{i j}, i ≤ j -> image_chain f g j ⊆ image_chain f g i := by
  intro i j h
  induction j generalizing i with
  | zero => cases Nat.le_zero.mp h; rfl
  | succ j ih =>
    replace h := Nat.lt_or_eq_of_le h
    rcases h with h | h
    replace h := Nat.le_of_lt_succ h
    apply Set.sub_trans _ (ih h)
    apply image_chain_sub_succ
    subst i; rfl

noncomputable def schroder_bernstein'
  [LEM] (f: α ↪ β) (g: β ↪ α) (a: α) : β :=
  let D := ⨅ i, image_chain f g i
  -- have top_eq : ⊤ = (⊤ \ image_chain f g 0) ∪ (⨆i, (image_chain f g i) \ image_chain f g (i + 1)) ∪ D := by
  --   ext a; simp
  --   apply LEM.or_iff_not_imp_right.mpr
  --   intro h; simp [D] at h
  --   obtain ⟨i, hi⟩ := h
  --   apply LEM.or_iff_not_imp_left.mpr
  --   intro h₀; rw [LEM.not_not] at h₀
  --   induction i with
  --   | zero => contradiction
  --   | succ i ih =>
  --     rcases em (a ∈ image_chain f g i) with h | h
  --     exists i
  --     replace ih := ih h
  --     assumption
  -- have s₁_eq : image_chain f g 0 = (⨆i, (image_chain f g i) \ image_chain f g (i + 1)) ∪ D := by
  --   rw [←Set.inter_eq_right ⊤ (image_chain f g 0) (Set.sub_top _),
  --     top_eq]
  --   simp [Set.union_inter, Set.sdiff_inter]
  --   congr
  --   · rw [Set.iSup_inter]
  --     congr; ext1 i
  --     rw [Set.inter_eq_left]
  --     apply Set.sub_trans (Set.sdiff_sub _ _)
  --     apply image_chain_sub
  --     apply Nat.zero_le
  --   · ext i; simp [D]
  --     intro h; apply h
  -- have : () (g ∘ f)
  sorry

-- public noncomputable def schroder_bernstein
--   (f: α ↪ β) (g: β ↪ α) : Bijection α β where
--   toFun := schroder_bernstein' f g
--   injective := sorry
--   surjective := sorry
