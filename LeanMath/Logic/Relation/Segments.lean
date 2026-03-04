import LeanMath.Data.Set.Relation

variable {α β γ: Type*} {r: α -> α -> Prop} {s: β -> β -> Prop} {t: γ -> γ -> Prop}
  -- [Relation.IsWellOrder r] [Relation.IsWellOrder s] [Relation.IsWellOrder t]

def Relation.IsInitial (s: β -> β -> Prop) [FunLike F α β] (f: F) :=
  ∀a, ∀b, s b (f a) -> b ∈ Set.range f

def Relation.IsPrincipal (s: β -> β -> Prop) [FunLike F α β] (f: F) (top: β) :=
  ∀b, s b top ↔ b ∈ Set.range f

structure InitialSegment {α β: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends r ↪r s  where
  isInitial : Relation.IsInitial s toFun

structure PrincipalSegment {α β: Type*} (r: α -> α -> Prop) (s: β -> β -> Prop) extends r ↪r s  where
  isPrincipal : ∃top, Relation.IsPrincipal s toFun top

infixr:80 " ≼r " => InitialSegment
infixr:80 " ≺r " => PrincipalSegment

instance : EmbeddingLike (r ≼r s) α β where
instance : IsRelHom (r ≼r s) r s where

instance : EmbeddingLike (r ≺r s) α β where
instance : IsRelHom (r ≺r s) r s where

def InitialSegment.IsInitial (f: r ≼r s) : Relation.IsInitial s f := f.isInitial
def PrincipalSegment.IsPrincipal (f: r ≺r s) : ∃top, Relation.IsPrincipal s f top := f.isPrincipal

def InitialSegment.id (r: α -> α -> Prop) : r ≼r r where
  toRelEmbedding := RelEmbedding.id _
  isInitial := by
    intro a b h
    exists b

def PrincipalSegment.toInitialSegment [Relation.IsTrans s] (f: r ≺r s) : r ≼r s where
  toRelEmbedding := f.toRelEmbedding
  isInitial := by
    intro a b h
    replace  h : s _ (f a) := h
    have ⟨top, hf⟩ := f.IsPrincipal
    have sa := (hf (f a)).mpr Set.mem_range'
    exact (hf b).mp (Relation.trans h sa)

@[simp] def InitialSegment.apply_toRelEmbedding (f: r ≼r s) (x: α) : f.toRelEmbedding x = f x := rfl

def InitialSegment.trans (f: r ≼r s) (g: s ≼r t) : r ≼r t where
  toRelEmbedding := f.toRelEmbedding.trans g.toRelEmbedding
  isInitial := by
    intro a b h
    simp
    replace h : t _ (g (f _)) := h
    obtain ⟨_, _, rfl⟩ := g.IsInitial _ _ h
    replace h := (map_rel g).mpr h
    obtain ⟨x, _, rfl⟩ := f.IsInitial _ _ h
    replace h := (map_rel f).mpr h
    exists x

def PrincipalSegment.trans [Relation.IsTrans t] (f: r ≺r s) (g: s ≺r t) : r ≺r t where
  toRelEmbedding := f.toRelEmbedding.trans g.toRelEmbedding
  isPrincipal := by
    have ⟨top, htop⟩ := f.IsPrincipal
    have ⟨top', htop'⟩ := g.IsPrincipal
    exists g top; intro b
    apply Iff.intro
    · intro tb
      have ttop := (htop' (g top)).mpr Set.mem_range'
      obtain ⟨b, _, rfl⟩ := (htop' b).mp (Relation.trans tb ttop)
      have sb := map_rel_rev g tb
      obtain ⟨b, _, rfl⟩ := (htop b).mp sb
      apply Set.mem_range'
    · rintro ⟨b, _, rfl⟩
      apply map_rel_fwd g
      apply (htop _).mpr
      apply Set.mem_range'

instance [Relation.IsWelFounded s] [Relation.IsTrichotomous s (· = ·)] : Subsingleton (r ≼r s) where
  allEq a b := by
    have := a.toRelEmbedding.liftWellfounded
    apply DFunLike.ext
    intro  x
    induction x using (Relation.wf r).induction with
    | h x ih =>
    rcases Relation.trichotomous s (a x) (b x) with h | h | h
    · have ⟨y, _, g⟩ := b.IsInitial x (a x) h
      rw [g] at h
      have := ih y (map_rel_rev _ h)
      rw [←ih y (map_rel_rev _ h)] at g
      cases a.inj g
      have := Relation.irrefl h
      contradiction
    · assumption
    · have ⟨y, _, g⟩ := a.IsInitial _ _ h
      rw [g] at h
      rw [ih _ (map_rel_rev _ h)] at g
      cases b.inj g
      have := Relation.irrefl h
      contradiction

instance [Relation.IsWellOrder s] : Subsingleton (r ≺r s) where
  allEq a b := by
    have h : a.toInitialSegment = b.toInitialSegment := Subsingleton.allEq _ _
    cases a; cases b
    cases h
    rfl

def InitialSegment.eq [Relation.IsWelFounded s] [Relation.IsTrichotomous s (· = ·)] (f g: r ≼r s) : ∀x, f x = g x := by
  apply congrFun
  congr; apply Subsingleton.allEq

def PrincipalSegment.eq [Relation.IsWellOrder s] (f g: r ≺r s) : ∀x, f x = g x := by
  apply congrFun
  congr; apply Subsingleton.allEq

def PrincipalSegment.irrefl [Relation.IsWellOrder r] (f: r ≺r r) : False := by
  have eq : ∀x, f x = x := InitialSegment.eq f.toInitialSegment (InitialSegment.id _)
  have ⟨top, htop⟩ := f.IsPrincipal
  have := (htop top).mpr; simp at this
  replace this := this top; rw [eq top] at this
  exact Relation.irrefl (this rfl)

def RelEquiv.toInitialSegment (f: r ≃r s) : r ≼r s where
  toFun := f
  inj := f.inj
  map_rel := map_rel f
  isInitial := by
    intro a b h
    rw [←f.symm_coe b]
    apply Set.mem_range'

def InitialSegment.principal_or_eqv [Relation.IsWellOrder s] (f: r ≼r s) : Nonempty (r ≺r s) ∨ Nonempty (r ≃r s) := by
  apply Classical.or_iff_not_imp_left.mpr
  intro h
  have hf : ¬∃top, Relation.IsPrincipal s f top := fun hf => h ⟨{
    toRelEmbedding := f.toRelEmbedding
    isPrincipal := hf
  }⟩
  simp [Relation.IsPrincipal] at hf
  have hb (b: β) : ∃a, b = f a := by
    induction b using (Relation.wf s).induction with
    | _ b ih =>
    have ⟨a, ha⟩ := hf b
    by_cases sab:s a b
    · replace ha := fun h => ha ⟨fun _ => h, fun _ => sab⟩
      simp at ha
      obtain ⟨_, rfl⟩ := ih a sab
      nomatch ha _ rfl
    · simp [sab] at ha
      obtain ⟨a, rfl⟩ := ha
      rcases Relation.trichotomous s (f a) b with g | g | g
      contradiction
      exists a; symm; assumption
      have := f.IsInitial a b g
      simpa using this
  clear hf
  obtain ⟨g, hg⟩ := Classical.axiomOfChoice hb
  refine ⟨?_⟩
  exact {
    toFun := f
    invFun := g
    leftInv _ := (hg _).symm
    rightInv _ := by
      apply f.inj
      show f _ = _
      rw [←hg]
      rfl
    map_rel := map_rel f
  }

def InitialSegment.trans_princ [Relation.IsWellOrder t] (f: r ≼r s) (g: s ≺r t) : r ≺r t where
  toRelEmbedding := f.toRelEmbedding.trans g.toRelEmbedding
  isPrincipal := by
    have := g.toRelEmbedding.liftWellOrder
    have := f.toRelEmbedding.liftWellOrder
    -- have ⟨top, htop⟩ := g.IsPrincipal
    have h : ∃x, ∀a, t (g (f a)) x := by
      have ⟨top, htop⟩ := g.IsPrincipal
      exists top
      intro a
      apply (htop _).mpr
      apply Set.mem_range'
    let top := Relation.min t h
    have htop := Relation.min_spec t h
    have top_min := Relation.min_minimal t h
    exists top
    intro b
    symm; apply Iff.intro
    · simp; intro _ rfl
      apply htop
    · simp; intro hb
      have := top_min _ hb
      simp at this
      let a := Relation.min r this
      have ha := Relation.min_spec r this
      have a_min : ∀x, r x a -> _ := Relation.min_minimal r this
      simp at a_min
      exists a
      rcases Relation.trichotomous t b (g (f a)) with h | h | h
      · have := a_min
        obtain ⟨b, _, rfl⟩ := g.toInitialSegment.IsInitial _ _ h
        obtain ⟨b, _, rfl⟩ := f.IsInitial _ _ (map_rel_rev g h)
        show g _ = g (f _); congr
        nomatch Relation.irrefl (a_min b (map_rel_rev f (map_rel_rev g h)))
      · assumption
      · nomatch ha h

def PrincipalSegment.trans_init [Relation.IsTrans t] (f: r ≺r s) (g: s ≼r t) : r ≺r t where
  toRelEmbedding := f.toRelEmbedding.trans g.toRelEmbedding
  isPrincipal := by
    have := g.toRelHom.liftTrans
    have := f.toRelHom.liftTrans
    have ⟨top, htop⟩ := f.IsPrincipal
    exists g top
    intro b
    apply Iff.intro
    · intro h
      simp; show ∃i, b = g (f _)
      obtain ⟨b, _, rfl⟩ := g.IsInitial _ _ h
      replace h := map_rel_rev g h
      have ⟨i, _, hi⟩ := (htop _).mp h
      exists i
      rw [hi]
    · rintro ⟨a, _, rfl⟩
      show t (g (f a)) _
      apply map_rel_fwd
      apply (htop _).mpr
      apply Set.mem_range'

def InitialSegment.antisymm [Relation.IsWellOrder s] (f: r ≼r s) (g: s ≼r r) : r ≃r s where
  toFun := f
  invFun := g
  map_rel := map_rel f
  leftInv := by
    have := f.liftWellOrder
    have alleq := Subsingleton.allEq (g.trans f) (.id _)
    intro x
    show (g.trans f) x = x
    rw [alleq]; rfl
  rightInv := by
    have := f.liftWellOrder
    have alleq := Subsingleton.allEq (f.trans g) (.id _)
    intro x
    show (f.trans g) x = x
    rw [alleq]; rfl

private def Relation.IsPrincipal.unique' (s: β -> β -> Prop) [Relation.IsWellOrder s] (f: r ≺r s) :
  Relation.IsPrincipal s f a ->
  Relation.IsPrincipal s f b ->
  ¬s a b := by
  intro ha hb h
  obtain ⟨a, _, rfl⟩ := (hb a).mp h
  obtain g := (ha (f a)).mpr Set.mem_range'
  exact Relation.irrefl g

def Relation.IsPrincipal.unique (s: β -> β -> Prop) [Relation.IsWellOrder s] (f: r ≺r s) :
  Relation.IsPrincipal s f a ->
  Relation.IsPrincipal s f b ->
  a = b := by
  intro ha hb
  rcases Relation.trichotomous s a b with h | h | h
  · nomatch unique' s f ha hb h
  · assumption
  · nomatch unique' s f hb ha h

def Relation.IsPrincipal.trans_init [Relation.IsWellOrder t] (f: r ≺r s) (g: s ≼r t) :
  Relation.IsPrincipal s f a ->
  Relation.IsPrincipal t (f.trans_init g) (g a) := by
  intro ha i
  apply Iff.intro
  · intro h
    obtain ⟨i, _, rfl⟩ := g.IsInitial _ _ h
    replace h := map_rel_rev g h
    obtain ⟨i, _, rfl⟩ := (ha i).mp h
    apply Set.mem_range'
  · rintro ⟨i, _, rfl⟩
    apply map_rel_fwd g
    show s (f i) a
    apply (ha _).mpr
    apply Set.mem_range'

namespace PrincipalSegment

variable [Relation.IsWellOrder r] [Relation.IsWellOrder s]

private noncomputable def collapse_helper [Relation.IsWellOrder r] (f: r ↪r s) (a: α) : { b: β // ¬ s (f a) b } :=
  let U: Set β := Set.ofMem fun b => ∀x (h: r x a), s (collapse_helper f x) b
  have : U.Nonempty := by
    exists f a
    · intro x hx'
      rcases Relation.trichotomous s (collapse_helper f x).val (f x) with hx | hx | hx
      · apply Relation.trans hx (map_rel_fwd f hx')
      · rw [hx]; exact map_rel_fwd f hx'
      · have := (collapse_helper f x).property
        contradiction
  ⟨Set.min s this, by
    apply Set.min_minimal
    intro x rxa
    rcases Relation.trichotomous s (collapse_helper f x).val (f x) with hx | hx | hx
    · apply Relation.trans hx
      apply map_rel_fwd
      assumption
    · rw [hx]
      apply map_rel_fwd
      assumption
    · have:= (collapse_helper f x).property
      contradiction⟩
termination_by WellFounded.wrap r a

private def collapse_helper_lt (f: r ↪r s) : ∀b a, r a b -> s (collapse_helper f a) (collapse_helper f b) := by
  intro b
  show (collapse_helper f b).1 ∈ Set.ofMem fun a => ∀x (_ : r x b), s (collapse_helper f x).1 a
  conv => { rhs; unfold collapse_helper }
  dsimp; apply Set.min_mem

private def collapse_helper_not_lt [Relation.IsWellOrder s] (f : r ↪r s) (a : α) {b}
  (h : ∀x (_: r x a), s (collapse_helper f x).1 b) : ¬s b (collapse_helper f a).1 := by
  let U := Set.ofMem fun b => ∀x (_ : r x a), s (collapse_helper f x).1 b
  unfold collapse_helper
  dsimp; apply Set.min_minimal s
  apply h

noncomputable def collapse (f: r ↪r s) : r ≼r s where
  toFun a := (collapse_helper f a).val
  inj := by
    intro a b h
    dsimp at h
    rcases Relation.trichotomous r a b with g | g | g
    · have := collapse_helper_lt f _ _ g
      rw [h] at this
      nomatch Relation.irrefl this
    · assumption
    · have := collapse_helper_lt f _ _ g
      rw [h] at this
      nomatch Relation.irrefl this
  map_rel := by
    intro a b
    apply Iff.intro
    apply collapse_helper_lt
    intro h
    rcases Relation.trichotomous r a b with g | rfl | g
    assumption
    nomatch Relation.irrefl h
    nomatch Relation.asymm (collapse_helper_lt f _ _ g) h
  isInitial := by
    intro a b h
    replace h : s b (collapse_helper f a).val := h
    simp
    show ∃i, b = (collapse_helper f i).val
    let S := Set.ofMem fun a => ¬s (collapse_helper f a).val b
    have : S.Nonempty := ⟨_, Relation.asymm h⟩
    exists S.min r this
    rcases Relation.trichotomous s b (collapse_helper f (Set.min r this)).val with g | g | g
    · exfalso
      refine collapse_helper_not_lt f _ ?_ g
      intro x hx
      apply Classical.byContradiction
      apply (Set.min_minimal r this x · hx)
    · assumption
    · exfalso
      have := Set.min_mem r this
      contradiction

end PrincipalSegment
