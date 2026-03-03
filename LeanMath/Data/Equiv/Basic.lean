import LeanMath.Data.Equiv.Defs
import LeanMath.Data.Bijection.Basic

namespace Equiv

def prod_equiv_pprod : α × β ≃ α ×' β where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  leftInv _ := rfl
  rightInv _ := rfl

def sum_equiv_psum : α ⊕ β ≃ α ⊕' β where
  toFun
  | .inl x => .inl x
  | .inr x => .inr x
  invFun
  | .inl x => .inl x
  | .inr x => .inr x
  leftInv
  | .inl _ => rfl
  | .inr _ => rfl
  rightInv
  | .inl _ => rfl
  | .inr _ => rfl

def optionCongr (f: α ≃ β) : Option α ≃ Option β where
  toFun
  | .some a => .some (f a)
  | .none => .none
  invFun
  | .some a => .some (f.symm a)
  | .none => .none
  leftInv := by
    intro a; cases a
    rfl
    show some _ = some _
    rw [f.symm_coe]
  rightInv := by
    intro a; cases a
    rfl
    show some _ = some _
    rw [f.coe_symm]

@[simp] def apply_optionCongr_none (f: α ≃ β) : optionCongr f .none = .none := rfl
@[simp] def symm_apply_optionCongr_none (f: α ≃ β) : (optionCongr f).symm .none = .none := rfl
@[simp] def apply_optionCongr_some (f: α ≃ β) (a: α) : optionCongr f (.some a) = .some (f a) := rfl
@[simp] def symm_apply_optionCongr_some (f: α ≃ β) (b: β) : (optionCongr f).symm (.some b) = .some (f.symm b) := rfl

-- def psumCongr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : α₀ ⊕' β₀ ≃ α₁ ⊕' β₁ where
--   toFun
--   | .inl x => .inl (f x)
--   | .inr x => .inr (g x)
--   inj' := by
--     intro x y h
--     cases x <;> cases y <;> dsimp at *
--     replace h := f.inj (PSum.inl.inj h)
--     congr; contradiction
--     contradiction
--     replace h := g.inj (PSum.inr.inj h)
--     congr
--   surj' := by
--     intro x
--     rcases x with x | x
--     · have ⟨y, h⟩ := f.surj x
--       exists .inl y
--       rw [←h]
--     · have ⟨y, h⟩ := g.surj x
--       exists .inr y
--       rw [←h]

-- def pprodCongr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : α₀ ×' β₀ ≃ α₁ ×' β₁ where
--   toFun x := ⟨f x.fst, g x.snd⟩
--   inj' := by
--     intro x y h
--     replace h := PProd.mk.inj h
--     ext
--     exact f.inj h.left
--     exact g.inj h.right
--   surj' := by
--     intro ⟨a, b⟩
--     have ⟨a', ha⟩ := f.surj a
--     have ⟨b', hb⟩ := g.surj b
--     exists ⟨a', b'⟩
--     dsimp
--     rw [ha, hb]

-- def sumCongr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : α₀ ⊕ β₀ ≃ α₁ ⊕ β₁ where
--   toFun
--   | .inl x => .inl (f x)
--   | .inr x => .inr (g x)
--   inj' := by
--     intro x y h
--     cases x <;> cases y <;> dsimp at *
--     replace h := f.inj (Sum.inl.inj h)
--     congr; contradiction
--     contradiction
--     replace h := g.inj (Sum.inr.inj h)
--     congr
--   surj' := by
--     intro x
--     rcases x with x | x
--     · have ⟨y, h⟩ := f.surj x
--       exists .inl y
--       rw [←h]
--     · have ⟨y, h⟩ := g.surj x
--       exists .inr y
--       rw [←h]

-- def prodCongr (f: α₀ ≃ α₁) (g: β₀ ≃ β₁) : α₀ × β₀ ≃ α₁ × β₁ where
--   toFun x := (f x.fst, g x.snd)
--   inj' := by
--     intro x y h
--     replace h := Prod.mk.inj h
--     ext
--     exact f.inj h.left
--     exact g.inj h.right
--   surj' := by
--     intro (a, b)
--     have ⟨a', ha⟩ := f.surj a
--     have ⟨b', hb⟩ := g.surj b
--     exists (a', b')
--     dsimp
--     rw [ha, hb]

end Equiv
