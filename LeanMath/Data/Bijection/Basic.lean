import LeanMath.Data.Bijection.Defs
import LeanMath.Data.Embedding.Defs

instance : EmbeddingLike (α ↭ β) α β where
  coeEmbedding f := {
    toFun := f
    inj := f.inj
  }

namespace Bijection

def psum_congr (f: α₀ ↭ α₁) (g: β₀ ↭ β₁) : α₀ ⊕' β₀ ↭ α₁ ⊕' β₁ where
  toFun
  | .inl x => .inl (f x)
  | .inr x => .inr (g x)
  inj' := by
    intro x y h
    cases x <;> cases y <;> dsimp at *
    replace h := f.inj (PSum.inl.inj h)
    congr; contradiction
    contradiction
    replace h := g.inj (PSum.inr.inj h)
    congr
  surj' := by
    intro x
    rcases x with x | x
    · have ⟨y, h⟩ := f.surj x
      exists .inl y
      rw [←h]
    · have ⟨y, h⟩ := g.surj x
      exists .inr y
      rw [←h]

def pprod_congr (f: α₀ ↭ α₁) (g: β₀ ↭ β₁) : α₀ ×' β₀ ↭ α₁ ×' β₁ where
  toFun x := ⟨f x.fst, g x.snd⟩
  inj' := by
    intro x y h
    replace h := PProd.mk.inj h
    ext
    exact f.inj h.left
    exact g.inj h.right
  surj' := by
    intro ⟨a, b⟩
    have ⟨a', ha⟩ := f.surj a
    have ⟨b', hb⟩ := g.surj b
    exists ⟨a', b'⟩
    dsimp
    rw [ha, hb]

def sum_congr (f: α₀ ↭ α₁) (g: β₀ ↭ β₁) : α₀ ⊕ β₀ ↭ α₁ ⊕ β₁ where
  toFun
  | .inl x => .inl (f x)
  | .inr x => .inr (g x)
  inj' := by
    intro x y h
    cases x <;> cases y <;> dsimp at *
    replace h := f.inj (Sum.inl.inj h)
    congr; contradiction
    contradiction
    replace h := g.inj (Sum.inr.inj h)
    congr
  surj' := by
    intro x
    rcases x with x | x
    · have ⟨y, h⟩ := f.surj x
      exists .inl y
      rw [←h]
    · have ⟨y, h⟩ := g.surj x
      exists .inr y
      rw [←h]

def prod_congr (f: α₀ ↭ α₁) (g: β₀ ↭ β₁) : α₀ × β₀ ↭ α₁ × β₁ where
  toFun x := (f x.fst, g x.snd)
  inj' := by
    intro x y h
    replace h := Prod.mk.inj h
    ext
    exact f.inj h.left
    exact g.inj h.right
  surj' := by
    intro (a, b)
    have ⟨a', ha⟩ := f.surj a
    have ⟨b', hb⟩ := g.surj b
    exists (a', b')
    dsimp
    rw [ha, hb]

def psigma_congr
  {α₀ α₁: Sort*} {β₀: α₀ -> Sort*} {β₁: α₁ -> Sort*} (ha: α₀ ↭ α₁) (hb: ∀a, β₀ a ↭ β₁ (ha a)): (Σ'a, β₀ a) ↭ (Σ'a, β₁ a) where
  toFun a := ⟨ha a.fst, hb _ a.snd⟩
  inj' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    replace ⟨ga, gb⟩ := PSigma.mk.inj h
    dsimp at ga gb
    cases inj ha ga
    have := inj (hb _) (eq_of_heq gb)
    congr
  surj' := by
    intro ⟨a, b⟩
    obtain ⟨a', rfl⟩ := ha.surj a
    obtain ⟨b', rfl⟩ := (hb a').surj b
    exists ⟨a', b'⟩

def bij_congr
  {α₀ α₁ β₀ β₁} (ha: α₁ ↭ α₀) (hb: β₀ ↭ β₁)
  : (α₀ ↭ β₀) -> (α₁ ↭ β₁) := fun f => hb.comp (f.comp ha)

def finsucc_poption (f: Fin n ↭ α) : Fin (n + 1) ↭ POption α where
  toFun
  | ⟨0, _⟩ => .none
  | ⟨n + 1, h⟩ => .some (f ⟨n, Nat.lt_of_succ_lt_succ h⟩)
  inj' := by
    intro i j h
    simp at h
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · nomatch h
    · nomatch h
    · rw [Fin.val_inj.mp <| Fin.mk.inj <| f.inj (POption.some.inj h)]
  surj' := by
    intro x; cases x
    exists 0
    rename_i x
    have ⟨i, hi⟩ := f.surj x
    exists i.succ
    show POption.some _ = .some _
    congr

@[simp] def apply_finsucc_poption_zero (f: Fin n ↭ α) : finsucc_poption f 0 = .none := rfl
@[simp] def apply_finsucc_poption_succ (f: Fin n ↭ α) (i: Fin n) : finsucc_poption f i.succ = .some (f i) := rfl

end Bijection
