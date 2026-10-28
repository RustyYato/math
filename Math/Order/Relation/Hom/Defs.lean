module

public import Math.Data.Hom.Defs
public import Math.Data.Embedding.Defs
public import Math.Data.Equiv.Defs
import Math.Logic.LEM
import Math.Tactic.Basic

namespace Math

section Hom

public class IsRelMap (F: Sort*) {α β: outParam Sort*} [Funlike F α β] (r: outParam <| α -> α -> Prop) (s: outParam <| β -> β -> Prop) : Prop where
  public map_rel (f: F) {a b: α}:  r a b -> s (f a) (f b) := by intro f; exact f.map_rel

public class IsRelHom (F: Sort*) {α β: outParam Sort*} [Funlike F α β] (r: outParam <| α -> α -> Prop) (s: outParam <| β -> β -> Prop) : Prop where
  public map_rel_iff (f: F) {a b: α}:  r a b ↔ s (f a) (f b) := by intro f; exact f.map_rel_iff

export IsRelMap (map_rel)
export IsRelHom (map_rel_iff)
public theorem map_rel_rev [Funlike F α β] [IsRelHom F r s] (f: F) {a b: α}: s (f a) (f b) -> r a b := (IsRelHom.map_rel_iff f).mpr

public instance [Funlike F α β] [IsRelHom F r s] : IsRelMap F r s where
  map_rel f := (map_rel_iff f).mp

public structure RelMap {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends Hom α β where
  protected map_rel {a b: α}:  r a b -> s (toFun a) (toFun b)

public structure RelHom {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends Hom α β where
  protected map_rel_iff {a b: α}:  r a b ↔ s (toFun a) (toFun b)

variable {α β γ: Sort*} {r: α -> α -> Prop} {s: β -> β -> Prop} {t: γ -> γ -> Prop}

public instance : Funlike (RelMap r s) α β where
public instance : Funlike (RelHom r s) α β where
public instance : IsRelMap (RelMap r s) r s where
public instance : IsRelHom (RelHom r s) r s where

public structure RelEmbedding {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends α ↪ β, RelHom r s where
public structure RelEquiv {α β: Sort*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends α ≃ β, RelHom r s where

public instance : EmbeddingLike (RelEmbedding r s) α β where
public instance : IsRelHom (RelEmbedding r s) r s where

public instance : EquivLike (RelEquiv r s) α β where
public instance : IsRelHom (RelEquiv r s) r s where

infixr:80 " →r₀ " => RelMap
infixr:80 " →r " => RelHom
infixr:80 " ↪r " => RelEmbedding
infixr:80 " ≃r " => RelEquiv


@[expose] public protected def RelMap.id (r: α -> α -> Prop) : r →r₀ r where
  toFun := id
  map_rel := id
@[expose] public protected def RelHom.id (r: α -> α -> Prop) : r →r r where
  toFun := id
  map_rel_iff := Iff.rfl
@[expose] public protected def RelEmbedding.id (r: α -> α -> Prop) : r ↪r r := {
  Embedding.id _, RelHom.id _ with
}
@[expose] public protected def RelEquiv.id (r: α -> α -> Prop) : r ≃r r := {
  Equiv.id _, RelHom.id _ with
}

@[expose] public def RelMap.comp (f: s →r₀ t) (g: r →r₀ s) : r →r₀ t where
  toFun := f ∘ g
  map_rel := map_rel f ∘ map_rel g
@[expose] public def RelHom.comp (f: s →r t) (g: r →r s) : r →r t where
  toFun := f ∘ g
  map_rel_iff := (map_rel_iff g).trans (map_rel_iff f)
@[expose] public def RelEmbedding.comp (f: s ↪r t) (g: r ↪r s) : r ↪r t := {
  Embedding.comp f.toEmbedding g.toEmbedding, RelHom.comp f.toRelHom g.toRelHom with
}
@[expose] public def RelEquiv.comp (f: s ≃r t) (g: r ≃r s) : r ≃r t := {
  Equiv.comp f.toEquiv g.toEquiv, RelHom.comp f.toRelHom g.toRelHom with
}

@[expose] public def RelMap.trans (f: r →r₀ s) (g: s →r₀ t) : r →r₀ t := comp g f
@[expose] public def RelHom.trans (f: r →r s) (g: s →r t) : r →r t := comp g f
@[expose] public def RelEmbedding.trans (f: r ↪r s) (g: s ↪r t) : r ↪r t := comp g f
@[expose] public def RelEquiv.trans (f: r ≃r s) (g: s ≃r t) : r ≃r t := comp g f

@[expose] public def RelEquiv.symm (f: r ≃r s) : s ≃r r := {
  f.toEquiv.symm with
  map_rel_iff := by
    intro a b
    apply Iff.trans _ (map_rel_iff f).symm
    dsimp; suffices ∀x, f (f.toEquiv.symm x) = x by rw [this, this]
    apply Equiv.symm_apply
}

namespace RelMap

@[ext] public theorem ext (f g: r →r₀ s) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

@[simp] public theorem apply_id : RelHom.id r x = x := rfl

@[simp] public theorem apply_comp (f: s →r₀ t) (g: r →r₀ s) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: r →r₀ s) (g: s →r₀ t) (x: α) : f.trans g x = g (f x) := rfl

@[simp] public theorem normalize_toEquiv (f: r →r₀ s) : f.toFun = f := rfl
@[simp] public theorem normalize_toFun (f: r →r₀ s) : f.toFun = f := rfl

end RelMap

namespace RelHom

@[ext] public theorem ext (f g: r →r s) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

@[simp] public theorem apply_id : RelHom.id r x = x := rfl

@[simp] public theorem apply_comp (f: s →r t) (g: r →r s) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: r →r s) (g: s →r t) (x: α) : f.trans g x = g (f x) := rfl

@[simp] public theorem normalize_toEquiv (f: r →r s) : f.toFun = f := rfl
@[simp] public theorem normalize_toFun (f: r →r s) : f.toFun = f := rfl

end RelHom

namespace RelEmbedding

@[ext] public theorem ext (f g: r ↪r s) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

@[simp] public theorem apply_id : RelEmbedding.id r x = x := rfl

@[simp] public theorem apply_comp (f: s ↪r t) (g: r ↪r s) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: r ↪r s) (g: s ↪r t) (x: α) : f.trans g x = g (f x) := rfl

public theorem inj (f: r ↪r s) : Function.Injective f := f.injective

@[simp] public theorem normalize_toEquiv (f: r ↪r s) : f.toFun = f := rfl
@[simp] public theorem normalize_toFun (f: r ↪r s) : f.toFun = f := rfl

end RelEmbedding

namespace RelEquiv

@[ext] public theorem ext (f g: r ≃r s) (h: ∀i, f i = g i) : f = g := DFunlike.ext f g h

@[simp] public theorem apply_id : RelEquiv.id r x = x := rfl

@[simp] public theorem apply_symm (f: r ≃r s) (x: α) : f.symm (f x) = x := f.rightInv _
@[simp] public theorem symm_apply (f: r ≃r s) (x: β) : f (f.symm x) = x := f.leftInv _
@[simp] public theorem symm_symm (f: r ≃r s) : f.symm.symm = f := rfl

@[simp] public theorem apply_comp (f: s ≃r t) (g: r ≃r s) (x: α) : f.comp g x = f (g x) := rfl
@[simp] public theorem apply_trans (f: r ≃r s) (g: s ≃r t) (x: α) : f.trans g x = g (f x) := rfl
@[simp] public theorem symm_comp (f: r ≃r s) : f.symm.comp f = RelEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]
@[simp] public theorem comp_symm (f: r ≃r s) : f.comp f.symm = RelEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem symm_trans (f: r ≃r s) : f.symm.trans f = RelEquiv.id _ := by
  ext a; dsimp; rw [symm_apply]
@[simp] public theorem trans_symm (f: r ≃r s) : f.trans f.symm = RelEquiv.id _ := by
  ext a; dsimp; rw [apply_symm]

public theorem inj (f: r ≃r s) : Function.Injective f := f.rightInv.injective
public theorem surj (f: r ≃r s) : Function.Surjective f := f.symm.rightInv.surjective

@[simp] public theorem normalize_toEquiv (f: r ≃r s) : f.toFun = f := rfl
@[simp] public theorem normalize_toFun (f: r ≃r s) : f.toFun = f := rfl

end RelEquiv

end Hom
