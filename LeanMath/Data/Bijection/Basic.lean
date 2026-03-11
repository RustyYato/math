import LeanMath.Data.Bijection.Defs

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

end Bijection
