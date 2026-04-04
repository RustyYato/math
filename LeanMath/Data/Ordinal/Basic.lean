import LeanMath.Data.Ordinal.Defs
import LeanMath.Data.Set.Finite
import LeanMath.Data.Set.WellFounded
import LeanMath.Data.Bijection.Basic
import LeanMath.Data.Fintype.Algebra.Monoid

namespace Ordinal

@[implicit_reducible]
private def well_order_finite_iso [LEM] (r: Fin n -> Fin n -> Prop) [Relation.IsWellOrder r] : Nonempty (r ≃r (· < ·: Fin n -> Fin n -> Prop)) := by
  induction n with
  | zero =>
    refine ⟨?_⟩
    exact {
      toEquiv := Equiv.empty
      map_rel {a} := elim_empty a
    }
  | succ n ih =>
    have hx : ∃x: Fin (n + 1), True := ⟨0, True.intro⟩
    have ⟨i, ⟨ht, hi⟩, hunique⟩ := Relation.exists_unique_min r hx; clear ht hunique

    replace hi : ∀b, ¬r b i := fun b hb => hi b hb True.intro
    let fi: Fin n ↪ Fin (n + 1) := Embedding.option_some.trans (Equiv.fin_erase i).symm.toEmbedding
    have ⟨eqv⟩ := ih (pullback_rel r fi)
    refine ⟨?_⟩
    apply RelEquiv.trans (pullback_rel_eqv r (
      (Equiv.option_congr eqv.symm.toEquiv).trans
      (Equiv.fin_erase i).symm)
    ).symm

    exact {
      toEquiv := (Equiv.fin_erase 0).symm
      map_rel {a b} := by
        cases a <;> cases b <;> simp [pullback_rel]
        · apply Relation.irrefl
        · rename_i a
          rcases Relation.trichotomous r i (if ↑(eqv.symm a) < i.val then (eqv.symm a).castSucc else (eqv.symm a).succ) with h | h | h
          · assumption
          · split at h <;> rename_i g
            rw [h] at g
            nomatch Nat.lt_irrefl _ g
            rw [h] at g
            nomatch g (Nat.lt_succ_self _)
          · nomatch hi _ h
        · rename_i b
          intro h
          exact hi _ h
        · rename_i a b
          have := map_rel eqv.symm (a := a) (b := b)
          symm; simpa [pullback_rel, fi] using this
    }

def finite {α: Type*} [LEM] [hfinite: Finite α] (r: α -> α -> Prop)
  [Relation.IsTrans r]
  [Relation.IsTrichotomous r (· = ·)]
  [Relation.IsIrrefl r] : ∃n: ℕ, type r = n := by
  have ⟨card, ⟨bij⟩⟩ := Finite.finBij α
  have eqv := Equiv.ofBij bij
  have reqv := pullback_rel_eqv r eqv
  exists card
  have ⟨_⟩ := well_order_finite_iso (pullback_rel r eqv)
  apply sound
  apply reqv.symm.trans
  apply RelEquiv.trans _ (ulift_rel_eqv_rel _).symm
  assumption

private def nonMin (r: α -> α -> Prop) : Set α where
  Mem a := ∃x, r x a

private def not_notMin_unqique {r: α -> α -> Prop} [Relation.IsTrichotomous r (· = ·)] (a b: α) (ha: ¬a ∈ nonMin r) (hb: ¬b ∈ nonMin r) : a = b := by
  rcases Relation.trichotomous r a b with h | h | h
  nomatch hb ⟨a, h⟩
  assumption
  nomatch ha ⟨b, h⟩

private def pow_ty (_: α -> α -> Prop) (s: β -> β -> Prop) :=
  { f : α -> β // Finite ((nonMin s).preimage f) }

variable {r: α -> α -> Prop} {s: β -> β -> Prop}

@[ext]
private def pow_ty.ext (f₀ f₁: pow_ty r s) :
  (∀x, f₀.val x = f₁.val x) -> f₀ = f₁ := by
  intro h;
  apply Subtype.ext
  ext; apply h

private def pow_rel (r: α -> α -> Prop) (s: β -> β -> Prop) : pow_ty r s -> pow_ty r s -> Prop :=
  fun f g => ∃a, s (f.val a) (g.val a) ∧ ∀x, r a x -> f.val x = g.val x

def pow_ty.support (f: pow_ty r s) : Set α := (nonMin s).preimage f.val
def pow_ty.support_rel (f: pow_ty r s) : f.support -> f.support -> Prop := pullback_rel r Embedding.subtype_val

instance (f: pow_ty r s) : Finite f.support := f.property
instance (f: pow_ty r s) [Relation.IsWellOrder r] : Relation.IsWellOrder f.support_rel :=
  inferInstanceAs (Relation.IsWellOrder (pullback_rel r Embedding.subtype_val: f.support -> f.support -> Prop))

def pow_ty.all_eq_or_exist_max [LEM] [Relation.IsWellOrder r] [Relation.IsWellOrder s] (f: pow_ty r s) : (∀i j,f.val i = f.val j) ∧ (∀i x, ¬s x (f.val i)) ∨ ∃max ∈ f.support, ∀y ∈ f.support, ¬r max y := by
  rcases Or.symm (em (∃x, x ∈ f.support)) with h | h
  · rw [not_exists] at h
    left; apply And.intro; intro i j
    apply not_notMin_unqique (r := s)
    apply h
    apply h
    intro i x g
    apply h i
    exists x
  right
  let r': f.support -> f.support -> Prop := pullback_rel r Embedding.subtype_val
  have ⟨⟨max, mem_max⟩, ⟨t, h_max⟩, hu⟩ := Relation.exists_unique_min (flip r') (P := fun _ => True) (by
    obtain ⟨x, hx⟩ := h
    exists ⟨x, hx⟩)
  exists max
  apply And.intro
  assumption
  intro i hi hr
  apply h_max ⟨i, hi⟩
  exact hr
  trivial

private def pow_rel_of_small (f g: pow_ty r s)
  (a: α) (ha: s (f.val a) (g.val a))
  (hle: ∀a', r a a' -> ¬s (g.val a) (f.val a)) : pow_rel r s f g := by sorry

instance {r: α -> α -> Prop} {s: β -> β -> Prop} [LEM] [Relation.IsWellOrder r] [Relation.IsWellOrder s] : Relation.IsTrans (pow_rel r s) where
  trans {a b c} h g := by
    obtain ⟨x, h, heq⟩ := h
    obtain ⟨y, g, geq⟩ := g
    rcases Relation.trichotomous r x y with rxy | rfl | rxy
    · exists y
      apply And.intro
      rwa [heq y rxy]
      intro z hz
      rw [heq, geq]
      assumption
      apply Relation.trans <;> assumption
    · exists x; apply And.intro
      exact Relation.trans h g
      intro y hy
      rw [heq y, geq y]
      assumption
      assumption
    · exists x
      apply And.intro
      rwa [←geq _ rxy]
      intro z hz
      rw [heq, geq]
      apply Relation.trans <;> assumption
      assumption

instance {r: α -> α -> Prop} {s: β -> β -> Prop} [LEM] [Relation.IsWellOrder r] [Relation.IsWellOrder s] : Relation.IsTrichotomous (pow_rel r s) (· = ·) where
  trichotomous (f g) := by
    rcases Or.symm (em (∃x, f.val x ≠ g.val x)) with h | h
    · simp [-Classical.not_not, LEM.not_not] at h
      right; left; ext; apply h
    · have := f.property
      have := g.property
      let support : Set α := (nonMin s).preimage f.val ∪ (nonMin s).preimage g.val
      have : Finite support := inferInstance
      have ⟨n, hn⟩ := finite (support.Induced r)
      obtain ⟨a, ha⟩ := h
      have amem : a ∈ support := by
        rcases em (f.val a ∈ nonMin s) with h | h
        left; assumption
        rcases em (g.val a ∈ nonMin s) with h' | h'
        right; assumption
        have := not_notMin_unqique _ _ h h'
        contradiction
      have ⟨⟨i, imem⟩ , ⟨hi, imin⟩, uniq⟩ := Relation.exists_unique_min (support.Induced (flip r)) (P := fun x =>
        f.val x ≠ g.val x) ⟨⟨a, amem⟩, ha⟩
      clear a amem ha
      clear uniq
      simp only [Set.Induced, LEM.not_not, flip, Subtype.forall] at imin
      replace imin : ∀a, r i a -> f.val a = g.val a := by
        intro  a ha
        rcases em (a ∈ support) with h | h
        apply imin
        assumption
        assumption
        apply not_notMin_unqique (r := s) (f.val a) (g.val a)
        intro g; apply h
        left; assumption
        intro g; apply h
        right; assumption
      dsimp at hi
      rcases Relation.trichotomous s (f.val i) (g.val i) with h | h | h
      · left; exists i
      · contradiction
      · right; right; exists i
        apply And.intro h
        intro x hx
        rw [imin _ hx]

instance {r: α -> α -> Prop} {s: β -> β -> Prop} [LEM] [Relation.IsWellOrder r] [Relation.IsWellOrder s] : Relation.IsIrrefl (pow_rel r s) where
  irrefl {f} h := by
    obtain ⟨a, ha, heq⟩ := h
    exact Relation.irrefl ha

set_option pp.deepTerms false in
instance {r: α -> α -> Prop} {s: β -> β -> Prop} [LEM] [Relation.IsWellOrder r] [Relation.IsWellOrder s] : Relation.IsWellOrder (pow_rel r s) where
  wf := by
    apply wf_iff_exists_min.mpr
    intro S hS
    rcases em (∃f ∈ S, ∀x, x ∉ f.support) with ⟨f, memf, hf⟩ | hS'
    · exists f
      apply And.intro memf
      intro a ha ⟨i, hi, _⟩
      apply hf i
      exists a.val i
    · simp only [not_exists, not_and, LEM.not_forall, LEM.not_not] at hS'
      replace h (f: pow_ty r s) (hf: f ∈ S) : ∃a ∈ f.support, ∀b ∈ f.support, ¬r a b := by
        obtain ⟨a, ha⟩ := hS' f hf
        have ⟨⟨max, mem_max⟩, ⟨t, hmax⟩, u⟩ := Relation.exists_unique_min (flip f.support_rel) (P := fun _ => _) ⟨⟨a, ha⟩, True.intro⟩
        clear t u
        exists max
        apply And.intro
        assumption
        intro b hb rb
        exact hmax ⟨b, hb⟩ rb True.intro
      let M : Set α := {
        Mem a := ∃f ∈ S, a ∈ f.support ∧ ∀b ∈ f.support, ¬r a b
      }
      have Mnonempty : M.Nonempty := by
        obtain ⟨f, hf⟩ := hS
        have ⟨max, memmax, rmax⟩ := h f hf
        exists max
        exists f
      -- a₀ is the smallest max support value
      have ⟨a₀, mem_a₀, ha₀⟩ := wf_iff_exists_min.mp (Relation.wf r) M Mnonempty
      induction a₀ using (Relation.wf r).induction generalizing S with
      | _ a₀ ih =>
      -- all functions in S which have max support of a₀
      let X₀ : Set (pow_ty r s) := S ∩ { Mem f := ∀b ∈ f.support, ¬r a₀ b }
      have X₀_nonempty : X₀.Nonempty := by
        obtain ⟨f, hf, mem_a₀, ha₀⟩ := mem_a₀
        exists f
      -- the image of all functions which have max support a₀
      let V: Set β := X₀.image fun f => f.val a₀
      have Vnonempty: V.Nonempty := by
        obtain ⟨f, hf, mem_a₀, _⟩ := mem_a₀
        exists f.val a₀
        apply Set.mem_image'
        apply And.intro
        assumption
        assumption
      --
      have ⟨b₀, mem_b₀, hb₀⟩ := wf_iff_exists_min.mp (Relation.wf s) V Vnonempty
      let X₁ : Set (pow_ty r s) := X₀.sep fun f => f.val a₀ = b₀
      have X₁_nonempty : X₁.Nonempty := by
        obtain ⟨f, f_mem, hf⟩ := mem_b₀
        exists f
      let A' : Set α := { Mem a := r a a₀ }
      let F' := pow_ty (α := A') (β := β) (pullback_rel r Embedding.subtype_val) s
      let map : X₁ ↪ F' := {
        toFun f := {
          val x := f.val.val x.val
          property := by
            apply Finite.ofEmbed (β := f.val.support)
            exact {
              toFun x := {
                val := x.val
                property := x.property
              }
              inj := by
                intro ⟨⟨x, _⟩, _⟩ y h
                cases h; rfl
            }
        }
        inj := by
          intro ⟨f₀, hf₀⟩ ⟨f₁, hf₁⟩ h
          dsimp at h
          congr; ext x
          rcases Relation.trichotomous r x a₀ with h₀ | h₀ | h₀
          exact congrFun (Subtype.mk.inj h) ⟨x, h₀⟩
          subst x
          rw [hf₀.right, hf₁.right]
          apply not_notMin_unqique (r := s)
          intro g₀
          nomatch hf₀.left.right x g₀ h₀
          intro g₀
          nomatch hf₁.left.right x g₀ h₀
      }
      let U : Set (pow_ty r s) := {
        Mem f :=
          -- all functions which take on the minimum value at
          -- inputs larger or equal to a₀
          (∀x, ¬r x a₀ -> ∀b, ¬s b (f.val x)) ∧
          -- and are equal to some function in X₁ (i.e. small functions)
          -- on the domain of inputs smaller than a₀
          ∃f' ∈ X₁, ∀x, r x a₀ -> f.val x = f'.val x
      }
      have : Nonempty β := ⟨b₀⟩
      have ⟨minval, ⟨m, minval_spec⟩, u⟩ := Set.exists_unique_min s (Set.univ_nonempty β)
      clear m u
      have Unonempty : U.Nonempty := by
        have ⟨f, ⟨f_mem, hf₀⟩, hf₁⟩ := X₁_nonempty
        dsimp at hf₀ hf₁
        open UniqueChoice in
        exists {
          val x :=
            if r x a₀ then
              f.val x
            else
              minval
          property := by
            apply Set.finite_of_sub _ (s := f.support)
            intro x hx
            unfold pow_ty.support
            replace hx : (if _ then _ else _) ∈ nonMin s := hx
            split at hx
            assumption
            have ⟨b, hx⟩ := hx
            nomatch minval_spec _ True.intro hx
        }
        apply And.intro
        intro x hx b
        dsimp; rw [if_neg hx]
        apply minval_spec
        trivial
        exists f
        apply And.intro
        exact ⟨⟨f_mem, hf₀⟩, hf₁⟩
        intro x hx; dsimp
        rw [if_pos hx]
      rcases Or.symm (em (∃f ∈ U, ∀x, x ∉ f.support)) with h | ⟨f, memf, hf⟩
      · simp only [not_exists, not_and, LEM.not_forall, LEM.not_not] at h
        replace h (f: pow_ty r s) (hf: f ∈ U) : ∃a ∈ f.support, ∀b ∈ f.support, ¬r a b := by
          obtain ⟨a, ha⟩ := h f hf
          have ⟨⟨max, mem_max⟩, ⟨t, hmax⟩, u⟩ := Relation.exists_unique_min (flip f.support_rel) (P := fun _ => _) ⟨⟨a, ha⟩, True.intro⟩
          clear t u
          exists max
          apply And.intro
          assumption
          intro b hb rb
          exact hmax ⟨b, hb⟩ rb True.intro
        let M' : Set α := {
          Mem a := ∃f ∈ U, a ∈ f.support ∧ ∀b ∈ f.support, ¬r a b
        }
        have M'_nonempty : M'.Nonempty := by
          obtain ⟨f, hf⟩ := Unonempty
          have ⟨max, memmax, rmax⟩ := h f hf
          exists max
          exists f
        have ⟨a₁, mem_a₁, ha₁⟩ := wf_iff_exists_min.mp (Relation.wf r) M' M'_nonempty
        have ra : r a₁ a₀ := by
          rcases em (r a₁ a₀) with ha | ha
          assumption
          · obtain ⟨f, hf, mem_support, max_support⟩ := mem_a₁
            obtain ⟨hf, _⟩ := hf
            have := hf a₁ ha
            obtain ⟨b, hb⟩ := mem_support
            nomatch this _ hb
        clear A' F' map
        have ⟨protof, protof_mem_U, hprotof⟩ := ih a₁ ra U Unonempty ?_ ?_ ?_ ?_ ?_
        all_goals
          clear ih
        · obtain ⟨protof_eq_min_of_ge, f, f_mem, protof_eq⟩ := protof_mem_U
          exists f; apply And.intro
          exact f_mem.left.left
          intro g g_mem_S hg
          rcases em (g ∈ X₁) with g_mem_X₁ | g_not_mem_X₁
          · sorry
          · simp only [Set.mem_sep, Set.mem_inter, g_mem_S, Set.ofMem_mem,
              true_and, X₁, X₀] at g_not_mem_X₁
            rw [and_comm, not_and] at g_not_mem_X₁
            rcases Relation.trichotomous s (g.val a₀) b₀ with h₁ | h₁ | h₁
            · rcases em (g ∈ X₀) with h₂ | h₂
              · apply hb₀ _ _ h₁
                apply Set.mem_image'
                assumption
              · simp only [true_and, g_mem_S, Set.mem_inter, Set.ofMem_mem,
                  LEM.not_forall, LEM.not_not, X₀] at h₂
                obtain ⟨a', a'_mem, ha'⟩ := h₂
                apply Relation.asymm hg
                apply pow_rel_of_small _ _ a'
                have := f_mem.right
                simp at this
                have := (f_mem.left.right a' · ha')
                rcases Relation.trichotomous s (f.val a') (g.val a') with h₂ | h₂ | h₂
                assumption
                obtain ⟨b, hb⟩ := a'_mem
                rw [←h₂] at hb
                nomatch this ⟨_, hb⟩
                nomatch this ⟨_, h₂⟩
                intro a'' ra'' sa'
                exact (f_mem.left.right a' · ha') ⟨_, sa'⟩
            · replace g_not_mem_X₁ := g_not_mem_X₁ h₁
              simp only [LEM.not_forall, LEM.not_not] at g_not_mem_X₁
              obtain ⟨a', a'_mem, ha'⟩ := g_not_mem_X₁
              apply Relation.asymm hg
              apply pow_rel_of_small _ _ a'
              have := f_mem.right
              simp at this
              have := (f_mem.left.right a' · ha')
              rcases Relation.trichotomous s (f.val a') (g.val a') with h₂ | h₂ | h₂
              assumption
              obtain ⟨b, hb⟩ := a'_mem
              rw [←h₂] at hb
              nomatch this ⟨_, hb⟩
              nomatch this ⟨_, h₂⟩
              intro a'' ra'' sa'
              exact (f_mem.left.right a' · ha') ⟨_, sa'⟩
            · clear g_not_mem_X₁
              apply Relation.asymm hg
              apply pow_rel_of_small _ _ a₀
              rwa [f_mem.right]
              intro a' ha' sa'
              rw [f_mem.right] at sa'
              exact Relation.asymm h₁ sa'
        · intro f hf
          have ⟨a, ha₀, ha₁⟩ := h f hf
          exists a
        · assumption
        · assumption
        · assumption
        · assumption
      · sorry

end Ordinal
