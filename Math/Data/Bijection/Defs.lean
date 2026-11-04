module

public import Math.Logic.Funlike
import Math.Tactic.Basic

namespace Math

public structure Bijection (α β: Sort*) where
  toFun: α -> β
  injection: Function.Injective toFun
  surjection: Function.Surjective toFun

namespace Bijection

public instance : Funlike (Bijection α β) α β where

@[expose] public protected def id (α: Sort*) : Bijection α α where
  toFun := id
  injection _ _ := id
  surjection _ := ⟨_, rfl⟩

variable {α β γ: Sort*}

@[ext] public theorem ext (f g: Bijection α β) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

@[simp] public theorem apply_id : Bijection.id α x = x := rfl

@[expose] public protected def comp (f: Bijection β γ) (g: Bijection α β) : Bijection α γ where
  toFun := f ∘ g
  injection := f.injection.comp g.injection
  surjection := f.surjection.comp g.surjection
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

public theorem inj (f: Bijection α β) : Function.Injective f := f.injection
public theorem surj (f: Bijection α β) : Function.Surjective f := f.surjection

@[simp] public theorem normalize_toFun (f: Bijection α β) : f.toFun = f := rfl
