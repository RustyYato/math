module

public import Math.Logic.Funlike
public import Math.Data.Embedding.Defs
import Math.Tactic.Basic

namespace Math

public structure Bijection (α β: Sort*) extends α ↪ β where
  surjective: Function.Surjective toFun

namespace Bijection

public instance : Funlike (Bijection α β) α β where

@[expose] public protected def id (α: Sort*) : Bijection α α where
  toFun := id
  injective _ _ := id
  surjective _ := ⟨_, rfl⟩

variable {α β γ: Sort*}

@[ext] public theorem ext (f g: Bijection α β) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

@[simp] public theorem apply_id : Bijection.id α x = x := rfl

@[expose] public protected def comp (f: Bijection β γ) (g: Bijection α β) : Bijection α γ where
  toFun := f ∘ g
  injective := f.injective.comp g.injective
  surjective := f.surjective.comp g.surjective
@[expose] public protected def trans (f: Bijection α β) (g: Bijection β γ) : Bijection α γ := g.comp f

@[simp] public theorem apply_comp (f: Bijection β γ) (g: Bijection α β) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: Bijection α β) (g: Bijection β γ) (x: α) : f.trans g x = g (f x) := rfl
-- @[simp] public theorem symm_comp (f: Bijection α β) : f.symm.comp f = Equiv.id _ := by
--   ext a; dsimp; rw [apply_symm]
-- @[simp] public theorem comp_symm (f: Bijection α β) : f.comp f.symm = Equiv.id _ := by
--   ext a; dsimp; rw [symm_apply]
-- @[simp] public theorem symm_trans (f: Bijection α β) : f.symm.trans f = Equiv.id _ := by
--   ext a; dsimp; rw [symm_apply]
-- @[simp] public theorem trans_symm (f: Bijection α β) : f.trans f.symm = Equiv.id _ := by
--   ext a; dsimp; rw [apply_symm]

public theorem inj (f: Bijection α β) : Function.Injective f := f.injective
public theorem surj (f: Bijection α β) : Function.Surjective f := f.surjective

@[simp] public theorem normalize_toFun (f: Bijection α β) : f.toFun = f := rfl
