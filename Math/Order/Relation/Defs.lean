module

public import Math.Data.Hom.Defs
public import Math.Data.Embedding.Defs
public import Math.Data.Equiv.Defs
public import Math.Logic.UniqueChoice
public import Math.Logic.LEM
import Math.Tactic.Basic

namespace Math

section Hom

public abbrev respects_rel (f: α -> β) (r: α -> α -> Prop) (s: β -> β -> Prop) : Prop := ∀{a b: α}, r a b -> s (f a) (f b)

public class IsRelMap (F: Sort*) {α β: outParam Sort*} [Funlike F α β] (r: outParam <| α -> α -> Prop) (s: outParam <| β -> β -> Prop) : Prop where
  public map_rel (f: F): respects_rel f r s := by intro f; exact f.map_rel

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

section Property

public class IsRefl (r: α -> α -> Prop) where
  refl (a: α): r a a

export IsRefl (refl)

public class IsSymm (r: α -> α -> Prop) where
  symm : r a b -> r b a

export IsSymm (symm)

public class IsTrans (r: α -> α -> Prop) where
  htrans : r a b -> r b c -> r a c

export IsTrans (htrans)

public instance [IsTrans r] : Trans r r r where
  trans := htrans

public class IsSetoid (r: α -> α -> Prop) extends IsRefl r, IsSymm r, IsTrans r where

public class IsConnected (R: α -> α -> Prop) (E: outParam <| α -> α -> Prop) where
  connected (a b: α) : R a b ∨ E a b ∨ R b a

export IsConnected (connected)

public class IsAntisymm (R: α -> α -> Prop) (E: outParam <| α -> α -> Prop) where
  antisymm (a b: α) : R a b -> R b a -> E a b

export IsAntisymm (antisymm)

public class IsTotal (R: α -> α -> Prop) where
  total (a b: α) : R a b ∨ R b a

export IsTotal (total)

public class IsIrrefl (R: α -> α -> Prop) where
  irrefl {a: α} : ¬R a a

export IsIrrefl (irrefl)

public class IsAsymm (R: α -> α -> Prop) where
  asymm {a b: α} : R a b -> R b a -> False

export IsAsymm (asymm)

public class IsWelFounded (R: α -> α -> Prop) where
  wf : WellFounded R

export IsWelFounded (wf)

public theorem wf_induction (r: α -> α -> Prop) [IsWelFounded r] : ∀{C : α → Prop} (a : α), (∀ (x : α), (∀ (y : α), r y x → C y) → C x) -> C a := @(wf (R := r)).induction

public class IsWellOrder (R: α -> α -> Prop) extends
  IsTrans R, IsWelFounded R, IsConnected R (· = ·)

public instance (priority := 500) [IsAsymm R] : IsIrrefl R where
  irrefl h := asymm h h
public instance (priority := 500) [IsIrrefl R] [IsTrans R] : IsAsymm R where
  asymm h g := irrefl (trans h g)
public instance [IsWelFounded R] : IsIrrefl R where
  irrefl := by
    intro a h
    induction a using (wf (R := R)).induction with
    | _ a ih =>
    exact ih a h h
public instance : IsTrans (Relation.TransGen r) where
  htrans := Relation.TransGen.trans
public instance [IsWelFounded R] : IsWelFounded (Relation.TransGen R) where
  wf := WellFounded.transGen wf
public instance [IsWelFounded R] : IsAsymm R where
  asymm h g := asymm (Relation.TransGen.single h) (Relation.TransGen.single g)

public instance : IsSetoid (α := α) (· = ·) where
  refl := Eq.refl
  symm := Eq.symm
  htrans := Eq.trans

public instance [s: Setoid α] : IsSetoid s.r where
  refl := s.refl
  symm := s.symm
  htrans := s.trans

public instance [s: Setoid α] : IsSetoid (α := α) (· ≈ ·) where
  refl := s.refl
  symm := s.symm
  htrans := s.trans

public instance (f: α -> β) (s: β -> β -> Prop) [IsRefl s] [IsSymm s] [IsTrans s] : IsSetoid (fun a b: α => s (f a) (f b)) where
  refl _ := refl _
  symm := symm
  htrans := trans

public theorem eqv (r: α -> α -> Prop) [IsRefl r] [IsSymm r] [IsTrans r] : Equivalence r where
  refl := refl
  symm := symm
  trans := trans

public abbrev setoid (r: α -> α -> Prop) [IsRefl r] [IsSymm r] [IsTrans r] : Setoid α where
  r := _
  iseqv := eqv r

end Property

section Generator

public inductive Relation.ReflGen (r: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflGen r a a
| of : r a b -> ReflGen r a b

public instance : IsRefl (Relation.ReflGen r) where
  refl := .refl

public inductive Relation.SymmGen (r: α -> α -> Prop) : α -> α -> Prop where
| of : r a b -> SymmGen r a b
| symm : r a b -> SymmGen r b a

public instance [IsRefl r] : IsRefl (Relation.SymmGen r) where
  refl h := .of (refl h)

public instance : IsSymm (Relation.SymmGen r) where
  symm
  | .of h => .symm h
  | .symm h => .of h

public inductive Relation.ReflTransGen (r: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : ReflTransGen r a a
| cons : r a b -> ReflTransGen r b c -> ReflTransGen r a c

public instance : IsRefl (Relation.ReflTransGen r) where
  refl := .refl
public instance : IsTrans (Relation.ReflTransGen r) where
  htrans := by
    intro a b c ab bc
    induction ab with
    | refl => assumption
    | cons _ _ ih =>
      apply Relation.ReflTransGen.cons
      assumption
      apply ih
      assumption

public theorem Relation.ReflTransGen.of {r: α -> α -> Prop} (h: r a b) : ReflTransGen r a b :=
  .cons h (.refl _)

public instance : IsRefl (Relation.ReflGen r) where
  refl := .refl

public inductive Relation.EquivGen (r: α -> α -> Prop) : α -> α -> Prop where
| refl (a: α) : EquivGen r a a
| symm : EquivGen r a b -> EquivGen r b a
| trans : EquivGen r a b -> EquivGen r b c -> EquivGen r a c
| of : r a b -> EquivGen r a b

public instance : IsRefl (Relation.EquivGen r) where
  refl := .refl
public instance : IsSymm (Relation.EquivGen r) where
  symm := .symm
public instance : IsTrans (Relation.EquivGen r) where
  htrans := .trans

end Generator

section Maps

variable {F α β: Sort*} {r: α -> α -> Prop} {s: β -> β -> Prop}

section ofReflGen

variable [IsRefl s]

@[expose] public def RelMap.ofReflGen [Funlike F α β] [IsRelMap F r s] (f: F) : Relation.ReflGen r →r₀ s where
  toFun := f
  map_rel
  | .refl _ => refl _
  | .of h => map_rel f h

@[expose] public def RelHom.ofReflGen [Funlike F α β] [IsRelHom F r s] (f: F) : Relation.ReflGen r →r s where
  toFun := f
  map_rel_iff {a b} := by
    apply Iff.intro
    intro h; cases h
    apply refl
    apply map_rel; assumption
    intro h
    apply Relation.ReflGen.of
    apply map_rel_rev f
    assumption

@[expose] public def RelEmbedding.ofReflGen [EmbeddingLike F α β] [IsRelHom F r s] (f: F) : Relation.ReflGen r ↪r s where
  toEmbedding := f
  map_rel_iff := map_rel_iff (RelHom.ofReflGen f)

@[expose] public def RelEquiv.ofReflGen [EquivLike F α β] [IsRelHom F r s] (f: F) : Relation.ReflGen r ≃r s where
  toEquiv := f
  map_rel_iff := map_rel_iff (RelHom.ofReflGen f)

end ofReflGen

section ofSymmGen

variable [IsSymm s]

@[expose] public def RelMap.ofSymmGen [Funlike F α β] [IsRelMap F r s] (f: F) : Relation.SymmGen r →r₀ s where
  toFun := f
  map_rel
  | .symm h => symm (map_rel f h)
  | .of h => map_rel f h

@[expose] public def RelHom.ofSymmGen [Funlike F α β] [IsRelHom F r s] (f: F) : Relation.SymmGen r →r s where
  toFun := f
  map_rel_iff {a b} := by
    apply Iff.intro
    intro h; cases h
    apply map_rel; assumption
    apply symm
    apply map_rel; assumption
    intro h
    apply Relation.SymmGen.of
    apply map_rel_rev f
    assumption

@[expose] public def RelEmbedding.ofSymmGen [EmbeddingLike F α β] [IsRelHom F r s] (f: F) : Relation.SymmGen r ↪r s where
  toEmbedding := f
  map_rel_iff := map_rel_iff (RelHom.ofSymmGen f)

@[expose] public def RelEquiv.ofSymmGen [EquivLike F α β] [IsRelHom F r s] (f: F) : Relation.SymmGen r ≃r s where
  toEquiv := f
  map_rel_iff := map_rel_iff (RelHom.ofSymmGen f)

end ofSymmGen

section ofTransGen

variable [IsTrans s]

@[expose] public def RelMap.ofTransGen [Funlike F α β] [IsRelMap F r s] (f: F) : Relation.TransGen r →r₀ s where
  toFun := f
  map_rel := by
    intro a b h
    induction h with
    | single h => apply map_rel f; assumption
    | tail _ h ih => exact Trans.trans ih (map_rel f h)

@[expose] public def RelHom.ofTransGen [Funlike F α β] [IsRelHom F r s] (f: F) : Relation.TransGen r →r s where
  toFun := f
  map_rel_iff {a b} := by
    apply Iff.intro
    apply map_rel (RelMap.ofTransGen f)
    intro h
    apply Relation.TransGen.single
    apply map_rel_rev f
    assumption

@[expose] public def RelEmbedding.ofTransGen [EmbeddingLike F α β] [IsRelHom F r s] (f: F) : Relation.TransGen r ↪r s where
  toEmbedding := f
  map_rel_iff := map_rel_iff (RelHom.ofTransGen f)

@[expose] public def RelEquiv.ofTransGen [EquivLike F α β] [IsRelHom F r s] (f: F) : Relation.TransGen r ≃r s where
  toEquiv := f
  map_rel_iff := map_rel_iff (RelHom.ofTransGen f)

end ofTransGen

section ofReflTransGen

variable [IsRefl s] [IsTrans s]

@[expose] public def RelMap.ofReflTransGen [Funlike F α β] [IsRelMap F r s] (f: F) : Relation.ReflTransGen r →r₀ s where
  toFun := f
  map_rel := by
    intro a b h
    induction h with
    | refl => apply refl
    | cons h _ ih => exact Trans.trans (map_rel f h) ih

@[expose] public def RelHom.ofReflTransGen [Funlike F α β] [IsRelHom F r s] (f: F) : Relation.ReflTransGen r →r s where
  toFun := f
  map_rel_iff {a b} := by
    apply Iff.intro
    apply map_rel (RelMap.ofReflTransGen f)
    intro h
    apply Relation.ReflTransGen.of
    apply map_rel_rev f
    assumption

@[expose] public def RelEmbedding.ofReflTransGen [EmbeddingLike F α β] [IsRelHom F r s] (f: F) : Relation.ReflTransGen r ↪r s where
  toEmbedding := f
  map_rel_iff := map_rel_iff (RelHom.ofReflTransGen f)

@[expose] public def RelEquiv.ofReflTransGen [EquivLike F α β] [IsRelHom F r s] (f: F) : Relation.ReflTransGen r ≃r s where
  toEquiv := f
  map_rel_iff := map_rel_iff (RelHom.ofReflTransGen f)

end ofReflTransGen

section ofEquivGen

variable [IsRefl s] [IsSymm s] [IsTrans s]

@[expose] public def RelMap.ofEquivGen [Funlike F α β] [IsRelMap F r s] (f: F) : Relation.EquivGen r →r₀ s where
  toFun := f
  map_rel := by
    intro a b h
    induction h with
    | of => apply map_rel f; assumption
    | refl => apply refl
    | symm => apply symm; assumption
    | trans _ _ ih₀ ih₁ => exact Trans.trans ih₀ ih₁

@[expose] public def RelHom.ofEquivGen [Funlike F α β] [IsRelHom F r s] (f: F) : Relation.EquivGen r →r s where
  toFun := f
  map_rel_iff {a b} := by
    apply Iff.intro
    apply map_rel (RelMap.ofEquivGen f)
    intro h
    apply Relation.EquivGen.of
    apply map_rel_rev f
    assumption

@[expose] public def RelEmbedding.ofEquivGen [EmbeddingLike F α β] [IsRelHom F r s] (f: F) : Relation.EquivGen r ↪r s where
  toEmbedding := f
  map_rel_iff := map_rel_iff (RelHom.ofEquivGen f)

@[expose] public def RelEquiv.ofEquivGen [EquivLike F α β] [IsRelHom F r s] (f: F) : Relation.EquivGen r ≃r s where
  toEquiv := f
  map_rel_iff := map_rel_iff (RelHom.ofEquivGen f)

end ofEquivGen

end Maps

section Min

variable (r: α -> α -> Prop) [IsWelFounded r] {P: α -> Prop}

public theorem exists_min [LEM] (h: ∃a, P a) : ∃a, P a ∧ ∀b, P b -> ¬r b a := by
  obtain ⟨a, pa⟩ := h
  induction a using wf_induction r with
  | _ a ih =>
  rcases em (∃b, P b ∧ r b a) with ⟨b, h, pb⟩ | ne
  exact ih b pb h
  refine ⟨a, pa, ?_⟩
  intro b pb h
  exact ne ⟨b, pb, h⟩

public theorem exists_unique_min [LEM] [IsConnected r (· = ·)] (h: ∃a, P a) : exists_unique (fun a => P a ∧ ∀b, P b -> ¬r b a) := by
  obtain ⟨a, pa⟩ := h
  induction a using wf_induction r with
  | _ a ih =>
  rcases em (∃b, P b ∧ r b a) with ⟨b, h, pb⟩ | ne
  exact ih b pb h
  refine ⟨a, ⟨pa, ?_⟩, ?_⟩
  intro b pb h
  exact ne ⟨b, pb, h⟩
  intro x ⟨px, h⟩
  have : ¬r x a := (ne ⟨x, px, ·⟩)
  have : ¬r a x := h a pa
  rcases connected (R := r) a x with _ | _ | _
  contradiction; assumption; contradiction

open Classical

namespace Relation

public noncomputable def arb_min (h: ∃a, P a) : α := Classical.choose (exists_min r h)
public theorem arb_min_spec (h: ∃a, P a) : P (arb_min r h) := (Classical.choose_spec (exists_min r h)).left
public theorem not_lt_arb_min (h: ∃a, P a) : ∀a, P a -> ¬r a (arb_min r h) := (Classical.choose_spec (exists_min r h)).right

variable [IsConnected r (· = ·)]

public noncomputable def min (h: ∃a, P a) : α := Classical.unique_choose (exists_unique_min r h)
public theorem min_spec (h: ∃a, P a) : P (min r h) := (Classical.unique_choose_spec (exists_unique_min r h)).left
public theorem not_lt_min (h: ∃a, P a) : ∀a, P a -> ¬r a (min r h) := (Classical.unique_choose_spec (exists_unique_min r h)).right
public theorem min_unique (h: ∃a, P a) (x: α) (px: P x) (not_lt: ∀a, P a -> ¬r a x) : min r h = x := Classical.unique_choose_unique (exists_unique_min r h) x ⟨px, not_lt⟩

end Relation

end Min

section Lift

public theorem lift_trans [Funlike F α β] [IsRelHom F r s] [IsTrans s] (f: F) : IsTrans r where
  htrans h g := map_rel_rev f <| trans (map_rel f h) (map_rel f g)

public theorem lift_symm [Funlike F α β] [IsRelHom F r s] [IsSymm s] (f: F) : IsSymm r where
  symm h := map_rel_rev f <| symm (map_rel f h)

public theorem lift_refl [Funlike F α β] [IsRelHom F r s] [IsRefl s] (f: F) : IsRefl r where
  refl _ := map_rel_rev f (refl _)

public theorem lift_wf [Funlike F α β] [IsRelMap F r s] [IsWelFounded s] (f: F) : IsWelFounded r where
  wf := by
    apply WellFounded.intro
    intro a
    induction h:f a using wf_induction s generalizing a with
    | _ b ih =>
    subst b
    apply Acc.intro
    intro b h
    exact ih (f b) (map_rel f h) _ rfl

public theorem lift_connected [EmbeddingLike F α β] [IsRelHom F r s] [IsConnected s (· = ·)] (f: F) : IsConnected r (· = ·) where
  connected a b := by
    rcases connected (R := s) (f a) (f b) with h | h | h
    left; apply map_rel_rev f; assumption
    right; left; apply Embedding.inj (f: α ↪ β) h
    right; right; apply map_rel_rev f; assumption
public theorem RelEmbedding.liftWellOrder (f: r ↪r s) [IsWellOrder s] : IsWellOrder r := {
  lift_trans f.toRelHom, lift_wf f.toRelHom, lift_connected f with
}

public theorem lift_total [EmbeddingLike F α β] [IsRelHom F r s] [IsTotal s] (f: F) : IsTotal r where
  total a b := by
    rcases total (R := s) (f a) (f b) with h | h
    · exact .inl <| map_rel_rev f h
    · exact .inr <| map_rel_rev f h

end Lift
