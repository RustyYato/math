import LeanMath.Logic.Funlike

structure Bijection (α β: Sort*) where
  toFun: α -> β
  protected inj': Function.Injective toFun
  protected surj': Function.Surjective toFun

infixr:20 " ↭ " => Bijection

namespace Bijection

instance : FunLike (α ↭ β) α β where

def inj (f: α ↭ β) : Function.Injective f := f.inj'
def surj (f: α ↭ β) : Function.Surjective f := f.surj'

protected def id (α: Sort*) : α ↭ α where
  toFun := id
  inj' _ _ := id
  surj' _ := ⟨_, rfl⟩

def comp (f: β ↭ γ) (g: α ↭ β) : α ↭ γ where
  toFun := f ∘ g
  inj':= Function.Injective.comp f.inj g.inj
  surj' := Function.Surjective.comp f.surj g.surj

abbrev trans (f: α ↭ β) (g: β ↭ γ) : α ↭ γ := g.comp f

@[simp] def apply_id (α: Sort*) (x: α) : Bijection.id α x = x := rfl
@[simp] def apply_comp (f: β ↭ γ) (g: α ↭ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_trans (f: β ↭ γ) (g: α ↭ β) (x: α) : (g.trans f) x = f (g x) := rfl

noncomputable def invFun (e: α ↭ β) : β -> α :=
  fun b => Classical.choose (e.surj b)
noncomputable def invFun_spec (e: α ↭ β) : ∀b, e (e.invFun b) = b :=
  fun b => Classical.choose_spec (e.surj b)

noncomputable def symm (f: α ↭ β) : β ↭ α where
  toFun := f.invFun
  inj' := by
    intro a b h
    obtain ⟨a, rfl⟩ := f.surj a
    obtain ⟨b, rfl⟩ := f.surj b
    have : f (f.invFun (f a)) = f (f.invFun (f b)) := by rw [h]
    rwa [invFun_spec, invFun_spec] at this
  surj' a := by
    exists f a
    apply f.inj
    rw [invFun_spec]

def symm_coe (f: α ↭ β) (x: β) : f (f.symm x) = x := by apply invFun_spec
def coe_symm (f: α ↭ β) (x: α) : f.symm (f x) = x := by
  apply f.inj
  apply invFun_spec

end Bijection
