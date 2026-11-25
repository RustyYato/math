module

public import Math.Order.Defs
public import Math.Data.Set.Defs
import Math.Order.Set

namespace Math

@[expose] public def IsInitial (f: α -> β) (s: β -> β -> Prop) : Prop :=
  ∀(a: α) (b: β), s b (f a) -> b ∈ Set.range f

@[expose] public def IsPrincipleAt (f: α -> β) (s: β -> β -> Prop) (b: β) : Prop :=
  ∀a, s a b ↔ a ∈ Set.range f
@[expose] public def IsPrinciple (f: α -> β) (s: β -> β -> Prop) : Prop :=
  ∃b: β, IsPrincipleAt f s b

public structure InitialSeg {α β: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends r →r s where
  protected isInitial : IsInitial toFun s

public structure PrincipleSeg {α β: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends r →r s where
  protected isPrinciple : IsPrinciple toFun s

public abbrev InitialSegLe (α β: Type*) [LE α] [LE β] := @InitialSeg α β (· ≤ ·) (· ≤ ·)
public abbrev PrincipleSegLt (α β: Type*) [LT α] [LT β] := @PrincipleSeg α β (· < ·) (· < ·)

infixr:80 " ≤i " => InitialSegLe
infixr:80 " ≼i " => InitialSeg
infixr:80 " ≺i " => PrincipleSeg

public instance (α β: Type*) [LE α] [LE β] : Funlike (α ≤i β) α β where
public instance (α β: Type*) [LE α] [LT α] [IsPartialOrder α] [LE β] [LT β] [IsPreorder β] : EmbeddingLike (α ≤i β) α β where
  coeInjective := by
    intro f a b h
    let f' : α →o β := f.toRelHom
    exact EmbeddingLike.coeInjective f' h

public instance {r: α -> α -> Prop} {s: β -> β -> Prop} : Funlike (r ≼i s) α β where
public instance {r: α -> α -> Prop} {s: β -> β -> Prop} : IsRelHom (r ≼i s) r s where

public instance {r: α -> α -> Prop} {s: β -> β -> Prop} : Funlike (r ≺i s) α β where
public instance {r: α -> α -> Prop} {s: β -> β -> Prop} : IsRelHom (r ≺i s) r s where


public instance
  {r: α -> α -> Prop}
  {s: β -> β -> Prop}
  [IsConnected r (· = ·)]
  [IsIrrefl s]
  : EmbeddingLike (r ≼i s) α β where
  coeInjective f {a b} hf := by
    rcases connected (R := r) a b with h | rfl | h
    nomatch irrefl (hf ▸ map_rel f h); rfl
    nomatch irrefl (hf ▸ map_rel f h)

@[ext] public theorem InitialSeg.ext {r: α -> α -> Prop} (f g: r ≼i s) (h: ∀i: α, f i = g i) : f = g :=
  DFunlike.ext _ _ h
@[ext] public theorem PrincipleSeg.ext {r: α -> α -> Prop} (f g: r ≺i s) (h: ∀i: α, f i = g i) : f = g :=
  DFunlike.ext _ _ h

@[expose] public def InitialSeg.of_eqv (f: r ≃r s) : r ≼i s where
  toRelHom := f.toRelHom
  isInitial := by
    show IsInitial f s
    intro a b h
    rw [←f.symm_apply b]
    apply Set.mem_range'

@[expose] public def InitialSeg.trans (f: r ≼i s) (g: s ≼i t) : r ≼i t where
  toRelHom := f.toRelHom.trans g.toRelHom
  isInitial := by
    show IsInitial (g ∘ f) t
    intro a b h
    obtain ⟨b, rfl⟩ := Set.mem_range.mp (g.isInitial _ _ h)
    obtain ⟨b, rfl⟩ := Set.mem_range.mp (f.isInitial _ _ (map_rel_rev g h))
    apply Set.mem_range'

@[simp] public theorem InitialSeg.apply_of_eqv (f: r ≃r s) : of_eqv f i = f i := rfl
@[simp] public theorem InitialSeg.apply_trans (f: r ≼i s) (g: s ≼i t) (i) : trans f g i = g (f i) := rfl

@[expose] public def PrincipleSeg.trans_init  (f: r ≺i s) (g: s ≼i t) : r ≺i t where
  toRelHom := f.toRelHom.trans g.toRelHom
  isPrinciple := by
    show IsPrinciple (g ∘ f) _
    have ⟨i, hi⟩ := f.isPrinciple
    exists g i; intro a
    apply Iff.intro
    intro h
    obtain ⟨a, rfl⟩ := g.isInitial _ _ h
    obtain ⟨a, rfl⟩ := (hi _).mp (map_rel_rev _ h)
    exists a
    rintro ⟨a, rfl⟩
    apply map_rel
    apply (hi _).mpr
    apply Set.mem_range'

@[expose] public def RelEquiv.trans_princ  (f: r ≃r s) (g: s ≺i t) : r ≺i t where
  toRelHom := f.toRelHom.trans g.toRelHom
  isPrinciple := by
    show IsPrinciple (g ∘ f) _
    have ⟨i, hi⟩ := g.isPrinciple
    exists i; intro a
    apply Iff.intro
    · intro h
      obtain ⟨i, rfl⟩ := (hi _).mp h
      rw [←f.symm_apply i]
      apply Set.mem_range'
    · rintro ⟨i, rfl⟩
      dsimp; apply (hi _).mpr
      apply Set.mem_range'

@[simp] public theorem PrincipleSeg.apply_trans_init  (f: r ≺i s) (g: s ≼i t) (i) : trans_init f g i = g (f i) := rfl
@[simp] public theorem RelEquiv.apply_trans_princ  (f: r ≃r s) (g: s ≺i t) (i) : trans_princ f g i = g (f i) := rfl

public def RelEquiv.congr_init (f: r₀ ≃r r₁) (g: s₀ ≃r s₁) : (r₀ ≼i s₀) ≃ (r₁ ≼i s₁) where
  toFun x := (InitialSeg.of_eqv f.symm).trans (x.trans (InitialSeg.of_eqv g))
  invFun x := (InitialSeg.of_eqv f).trans (x.trans (InitialSeg.of_eqv g.symm))
  leftInv _ := by ext i; simp
  rightInv _ := by ext i; simp

public def RelEquiv.congr_princ (f: r₀ ≃r r₁) (g: s₀ ≃r s₁) : (r₀ ≺i s₀) ≃ (r₁ ≺i s₁) where
  toFun x := f.symm.trans_princ (x.trans_init (InitialSeg.of_eqv g))
  invFun x := f.trans_princ (x.trans_init (InitialSeg.of_eqv g.symm))
  leftInv _ := by ext i; simp
  rightInv _ := by ext i; simp

instance [IsWellOrder r] [IsWellOrder s] : Subsingleton (r ≼i s) where
  allEq f g := by
    ext i
    induction i using (wf (R := r)).induction with
    | _ i ih =>
    rcases connected (R := s) (f i) (g i) with h | h | h
    · have ⟨j, hj⟩ := g.isInitial _ _ h
      rw [←hj] at h
      replace h := map_rel_rev _ h
      replace ih := ((ih _ h).trans hj)
      have := map_rel f h
      rw [ih] at this
      nomatch irrefl this
    · assumption
    · have ⟨j, hj⟩ := f.isInitial _ _ h
      rw [←hj] at h
      replace h := map_rel_rev _ h
      replace ih := (hj.symm.trans (ih _ h))
      have := map_rel g h
      rw [ih] at this
      nomatch irrefl this

public def RelEquiv.antisymm [IsWellOrder r] [IsWellOrder s] (f: r ≼i s) (g: s ≼i r) : r ≃r s where
  toRelHom := f.toRelHom
  invFun := g
  leftInv b := by
    show (g.trans f) b = b
    rw [Subsingleton.allEq (g.trans f) (InitialSeg.of_eqv (.id _))]
    rfl
  rightInv a := by
    show (f.trans g) a = a
    rw [Subsingleton.allEq (f.trans g) (InitialSeg.of_eqv (.id _))]
    rfl

@[expose] public def PrincipleSeg.toInitialSeg [IsTrans s] (f: r ≺i s) : r ≼i s where
  toRelHom := f.toRelHom
  isInitial := by
    change IsInitial f s
    have ⟨top, htop⟩ := f.isPrinciple
    intro a b h
    apply (htop b).mp
    apply htrans h
    apply (htop _).mpr
    apply Set.mem_range'

instance [IsWellOrder r] [IsWellOrder s] : Subsingleton (r ≺i s) where
  allEq f g := by
    ext i
    show f.toInitialSeg i = g.toInitialSeg i
    congr 1; apply Subsingleton.allEq

public protected theorem PrincipleSeg.irrefl [IsWellOrder r] (f: r ≺i r) : False := by
  have : f.toInitialSeg = InitialSeg.of_eqv (RelEquiv.id _) := Subsingleton.allEq _ _
  have ⟨top, htop⟩ := f.isPrinciple
  refine irrefl ((htop top).mpr ?_)
  show top ∈ Set.range f.toInitialSeg
  rw [this]
  exists top

public theorem InitialSeg.eqv_or_principal
  {r: α -> α -> Prop} {s: β -> β -> Prop}
  [LEM] [IsWellOrder s] (f: r ≼i s) :
  Function.Surjective f ∨ ∃b, ∀x, s x b ↔ x ∈ Set.range f := by
  apply LEM.or_iff_not_imp_left.mpr
  intro hf
  replace hf : ∃b, b ∉ Set.range f := by
    simp only [Function.Surjective, LEM.not_forall] at hf
    assumption
  replace hf := exists_min s hf
  have ⟨top, htop, top_min⟩ := hf
  exists top; intro b; apply Iff.intro
  · intro h
    exact LEM.not_not.mp (top_min _ · h)
  · intro h
    rcases connected (R := s) b top with _ | _ | top_lt
    assumption; subst b; contradiction
    exfalso
    obtain ⟨a, rfl⟩ := h
    have := (f.isInitial _ top top_lt)
    contradiction

noncomputable section

variable [LEM] {α β: Type*} {r: α -> α -> Prop} {s: β -> β -> Prop}
  [IsWellOrder s]

def collapse_helper (f: r ↪r s) : ∀a, { b // ¬s (f a) b } :=
  f.liftWellOrder.wf.fix fun a ih =>
      let S := Set.mk fun b => ∀a₀ h, s (ih a₀ h).val b
      have mem : f a ∈ S := by
        intro a₀ h₀
        rcases connected (R := s) (ih a₀ h₀) (f a) with h | h | h
        assumption
        · exfalso; apply (ih a₀ h₀).property
          rw [h]
          apply map_rel
          assumption
        · exfalso; apply (ih a₀ h₀).property
          apply htrans _ h
          apply map_rel
          assumption
      have : ∃x, x ∈ S := ⟨_, mem⟩
      {
        val := Set.unique_min _ s this
        property := (Set.not_lt_unique_min _ s this _ mem)
      }

theorem collapse_helper_lt (f: r ↪r s) : ∀a b, r b a -> s (collapse_helper f b) (collapse_helper f a) := by
  intro a
  unfold collapse_helper
  show (collapse_helper f a).val ∈ Set.mk fun b => ∀ (a') (_ : r a' a), s (collapse_helper f a').val b
  unfold collapse_helper; rw [WellFounded.fix_eq]
  dsimp; apply Set.unique_min_mem

theorem collapse_helper_not_lt (f : r ↪r s) (a : α) {b}
    (h : ∀ a' (_ : r a' a), s (collapse_helper f a').1 b) : ¬s b (collapse_helper f a).1 := by
  unfold collapse_helper; rw [WellFounded.fix_eq]
  dsimp only; apply Set.not_lt_unique_min
  assumption

public def InitialSeg.collapse (f: r ↪r s) : r ≼i s where
  toFun a := collapse_helper f a
  map_rel_iff {a b} := by
    have := f.liftWellOrder
    apply Iff.intro
    intro h
    apply collapse_helper_lt; assumption
    intro h
    rcases connected (R := r) a b with h | h | g
    · assumption
    · subst b; nomatch irrefl h
    · nomatch asymm (collapse_helper_lt f _ _ g) h
  isInitial := by
    have := f.liftWellOrder
    intro a b h
    dsimp at h
    let S := Set.mk fun a => ¬s (collapse_helper f a).val b
    have ex : ∃x, x ∈ S := ⟨_, asymm h⟩
    let a' := Set.unique_min S r ex
    exists a'
    dsimp
    rcases connected (R := s) (collapse_helper f a').val b with g | g | g
    · have := Set.unique_min_mem S r ex
      contradiction
    · assumption
    · exfalso; apply collapse_helper_not_lt f _ _ g
      intro a'' hr
      apply LEM.byContradiction
      intro h
      apply Set.not_lt_unique_min S r ex _ _ hr
      assumption

end
