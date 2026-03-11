import LeanMath.Logic.Funlike
import LeanMath.Data.Bijection.Defs
import LeanMath.Data.Embedding.Defs

structure Equiv (α β: Sort*) where
  toFun: α -> β
  invFun: β -> α
  leftInv: Function.LeftInverse toFun invFun
  rightInv: Function.RightInverse toFun invFun

infixr:50 " ≃ " => Equiv

class EquivLike (F: Sort*) (α β: outParam Sort*) where
  protected coeEquiv : F -> α ≃ β := by intro f; exact f.toEquiv
  protected coeInj : Function.Injective coeEquiv := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply EquivLike.coeInj
      assumption

--- This is not the interface for ops, just ensures that
--- all ops are implemented
set_option checkBinderAnnotations false in
class EquivOpsCheck (C: Sort u -> Sort u) (F: ∀α β (cα: C α) (cβ: C β), Sort v)
  [∀α β [cα: C α] [cβ: C β], EquivLike (F α β cα cβ) α β]
  where
  protected comp {α β γ: Sort u} [cα: C α] [cβ: C β] [cγ: C γ] : F β γ cβ cγ -> F α β cα cβ -> F α γ cα cγ
  protected trans {α β γ: Sort u} [cα: C α] [cβ: C β] [cγ: C γ] : F α β cα cβ -> F β γ cβ cγ -> F α γ cα cγ
  protected symm {α β: Sort u} [cα: C α] [cβ: C β] : F α β cα cβ -> F β α cβ cα
  protected refl (α: Sort u) [cα: C α] : F α α cα cα

instance {F α β: Sort*} [EquivLike F α β] : FunLike F α β where
  coeFun f := (EquivLike.coeEquiv (F := F) f).toFun
  coeInj := by
    intro a b h
    suffices EquivLike.coeEquiv a = EquivLike.coeEquiv b by
      exact EquivLike.coeInj this
    dsimp at h
    revert h;
    generalize EquivLike.coeEquiv a = a
    generalize EquivLike.coeEquiv b = b
    intro h
    suffices a.invFun = b.invFun by
      cases a; cases b
      congr
    ext x
    rw [←a.leftInv x, a.rightInv, h, b.rightInv]

namespace Equiv

instance : EquivLike (α ≃ β) α β where
  coeEquiv := id
  coeInj _ _ := id

protected def id (α: Sort*) : α ≃ α where
  toFun := id
  invFun := id
  leftInv _ := rfl
  rightInv _ := rfl

def symm (f: α ≃ β) : β ≃ α where
  toFun := f.invFun
  invFun := f.toFun
  leftInv := f.rightInv
  rightInv := f.leftInv

@[simp] def symm_coe (f: α ≃ β) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] def coe_symm (f: α ≃ β) (x: α) : f.symm (f x) = x := f.rightInv _

@[simp] def symm_symm (f: α ≃ β) : f.symm.symm = f := rfl

def comp (f: β ≃ γ) (g: α ≃ β) : α ≃ γ where
  toFun := f ∘ g
  invFun := g.symm ∘ f.symm
  leftInv x := by
    dsimp
    rw [g.symm_coe, f.symm_coe]
  rightInv x := by
    dsimp
    rw [f.coe_symm, g.coe_symm]

abbrev trans (f: α ≃ β) (g: β ≃ γ) : α ≃ γ := g.comp f

@[simp] def apply_toFun (f: α ≃ β) (x: α) : f.toFun x = f x := rfl

@[simp] def apply_id (α: Sort*) (x: α) : Equiv.id α x = x := rfl
@[simp] def apply_comp (f: β ≃ γ) (g: α ≃ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_trans (f: β ≃ γ) (g: α ≃ β) (x: α) : (g.trans f) x = f (g x) := rfl

@[simp] def trans_assoc (f: α ≃ β) (g: β ≃ γ) (h: γ ≃ γ') :
  f.trans (g.trans h) = (f.trans g).trans h := rfl

@[simp] def symm_trans (f: α ≃ β) : f.symm.trans f = .id _ := by
  apply DFunLike.ext; intro x
  simp
@[simp] def trans_symm (f: α ≃ β) : f.trans f.symm = .id _ := by
  apply DFunLike.ext; intro x
  simp
@[simp] def id_symm : (Equiv.id _).symm = (Equiv.id α) := rfl
@[simp] def id_trans (f: α ≃ β) : (Equiv.id _).trans f = f := rfl
@[simp] def trans_id (f: α ≃ β) : f.trans (Equiv.id _) = f := rfl

def inj (f: α ≃ β) : Function.Injective f := f.rightInv.injective
def surj (f: α ≃ β) : Function.Surjective f := f.symm.rightInv.surjective

def toBij (f: α ≃ β) : α ↭ β where
  toFun := f
  inj' := f.inj
  surj' := f.surj

@[simp] def apply_toBij (f: α ≃ β) : f.toBij x = f x := rfl

def toEmbedding (f: α ≃ β) : α ↪ β where
  toFun := f
  inj := f.inj

@[simp] def apply_toEmbedding (f: α ≃ β) : f.toEmbedding x = f x := rfl

class Nop (α: Sort u) where
instance : Nop α where
instance : EquivOpsCheck Nop (fun α β _ _ => α ≃ β) where
  comp := Equiv.comp
  trans := Equiv.trans
  symm := Equiv.symm
  refl α := Equiv.id α

def plift (α: Sort u) : α ≃ PLift α where
  toFun := PLift.up
  invFun := PLift.down
  leftInv _ := rfl
  rightInv _ := rfl

end Equiv

instance [EquivLike F α β] : EmbeddingLike F α β where
  coeEmbedding := Equiv.toEmbedding ∘ EquivLike.coeEquiv
  coeInj := by
    apply Function.Injective.comp
    · intro f g h
      suffices f.toFun = g.toFun by
        apply DFunLike.coeInj
        assumption
      obtain ⟨f, _, _, _⟩ := f
      obtain ⟨g, _, _, _⟩ := g
      cases h
      rfl
    · apply EquivLike.coeInj
