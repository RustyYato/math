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
        cases a <;> cases b <;> simp only [pullback_rel, Equiv.apply_comp, Equiv.apply_option_congr_some,
          RelEquiv.apply_toEquiv, Equiv.symm_fin_erase_some, Equiv.apply_toFun, Fin.val_zero, Nat.not_lt_zero,
          ↓reduceIte, Fin.succ_lt_succ_iff, Equiv.apply_option_congr_none, Equiv.symm_fin_erase_none,
          RelEquiv.apply_toEquiv, Fin.val_zero, Fin.succ_pos, iff_true, Fin.lt_irrefl, iff_false,
          Equiv.symm_fin_erase_none, Equiv.apply_toFun, Fin.not_lt_zero]
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
          symm; simpa only [pullback_rel, Embedding.apply_comp, Embedding.apply_option_some,
            Equiv.apply_toEmbedding, Equiv.symm_fin_erase_some, fi] using this
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

private def pow_rel_of_small [LEM] [Relation.IsWellOrder r] [Relation.IsWellOrder s] (f g: pow_ty r s)
  (a: α) (ha: s (f.val a) (g.val a))
  (hle: ∀a', r a a' -> ¬s (g.val a') (f.val a')) : pow_rel r s f g := by
  have ⟨⟨a', a'_mem_supp⟩, ⟨sa', ha'⟩, u⟩ := Relation.exists_unique_min (flip g.support_rel) (P := fun a => s (f.val a) (g.val a)) ⟨⟨a, _, ha⟩, ha⟩
  clear u; simp only [Subtype.forall] at sa' ha'
  replace ha' : ∀a, _ -> r a' a -> _ := ha'
  exists a'
  apply And.intro sa'
  intro x hx
  rcases Relation.trichotomous s (f.val x) (g.val x) with h | h | h
  nomatch ha' _ ⟨_, h⟩ hx h
  assumption; exfalso
  refine hle _ ?_ h
  rcases Relation.trichotomous r a a' with h | h | h
  exact Relation.trans h hx
  subst a'; assumption
  nomatch ha' _ ⟨_, ha⟩ h ha

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
    · simp only [ne_eq, not_exists, LEM.not_not] at h
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

instance {r: α -> α -> Prop} {s: β -> β -> Prop} [LEM] [Relation.IsWellOrder r] [Relation.IsWellOrder s] : Relation.IsWellOrder (pow_rel r s) where
  wf := by
    open UniqueChoice in
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
          · let g' : pow_ty r s := {
              val x :=
                if r x a₀ then
                  g.val x
                else
                  minval
              property := by
                apply Set.finite_of_sub _ (s := g.support)
                intro x hx
                unfold pow_ty.support
                replace hx : (if _ then _ else _) ∈ nonMin s := hx
                split at hx
                assumption
                have ⟨b, hx⟩ := hx
                nomatch minval_spec _ True.intro hx
            }
            have g'_in_U : g' ∈ U := by
              apply And.intro
              · intro x hx b hb
                unfold g' at hb
                simp only [hx, ↓reduceIte] at hb
                exact minval_spec _ True.intro hb
              · exists g; apply And.intro
                assumption
                intro x hx
                unfold g'; simp only [hx, ↓reduceIte]
            apply hprotof _ g'_in_U
            have ⟨a, g_lt_f, g_eq_f⟩ := hg
            have : r a a₀ := by
              rcases Relation.trichotomous r a a₀ with h | h | h
              assumption
              · subst a
                rw [g_mem_X₁.right, f_mem.right] at g_lt_f
                nomatch Relation.irrefl g_lt_f
              · have hg := (g_mem_X₁.left.right _ · h)
                have hf := (f_mem.left.right _ · h)
                rw [not_notMin_unqique (r := s) _ _ hg hf] at g_lt_f
                nomatch Relation.irrefl g_lt_f
            apply pow_rel_of_small
            show s (g'.val a) (protof.val a)
            simp only [this, ↓reduceIte, protof_eq _ this, g']
            assumption
            intro x hx hs
            have := g_eq_f _ hx
            dsimp [g'] at hs; split at hs <;> rename_i h
            rw [protof_eq _ h] at hs
            rw [this] at hs
            exact Relation.irrefl hs
            nomatch minval_spec _ True.intro hs
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
                have := (f_mem.left.right a' · ha')
                rcases Relation.trichotomous s (f.val a') (g.val a') with h₂ | h₂ | h₂
                assumption
                obtain ⟨b, hb⟩ := a'_mem
                rw [←h₂] at hb
                nomatch this ⟨_, hb⟩
                nomatch this ⟨_, h₂⟩
                intro a'' ra'' sa'
                exact (f_mem.left.right a'' · (Relation.trans ha' ra'')) ⟨_, sa'⟩
            · replace g_not_mem_X₁ := g_not_mem_X₁ h₁
              simp only [LEM.not_forall, LEM.not_not] at g_not_mem_X₁
              obtain ⟨a', a'_mem, ha'⟩ := g_not_mem_X₁
              apply Relation.asymm hg
              apply pow_rel_of_small _ _ a'
              have := (f_mem.left.right a' · ha')
              rcases Relation.trichotomous s (f.val a') (g.val a') with h₂ | h₂ | h₂
              assumption
              obtain ⟨b, hb⟩ := a'_mem
              rw [←h₂] at hb
              nomatch this ⟨_, hb⟩
              nomatch this ⟨_, h₂⟩
              intro a'' ra'' sa'
              exact (f_mem.left.right a'' · (Relation.trans ha' ra'')) ⟨_, sa'⟩
            · clear g_not_mem_X₁
              apply Relation.asymm hg
              apply pow_rel_of_small _ _ a₀
              rwa [f_mem.right]
              intro a' ha' sa'
              nomatch f_mem.left.right _ ⟨_, sa'⟩ ha'
        · intro f hf
          have ⟨a, ha₀, ha₁⟩ := h f hf
          exists a
        · assumption
        · assumption
        · assumption
        · assumption
      · clear ih
        obtain ⟨hf', f', f'_mem, feq⟩ := memf
        clear hf'; exists f'; apply And.intro
        exact f'_mem.left.left
        intro g hg g_lt_f
        obtain ⟨a₁, g_lt_f, g_eq_f⟩ := g_lt_f
        -- have := hf
        have : a₁ = a₀ := by
          rcases Relation.trichotomous r a₁ a₀ with ha | ha | ha
          · rw [←feq _ ha] at g_lt_f
            nomatch hf _ ⟨_, g_lt_f⟩
          · assumption
          · nomatch f'_mem.left.right _ ⟨_, g_lt_f⟩ ha
        subst a₁
        rw [f'_mem.right] at g_lt_f
        -- have ⟨a₁, a₁_mem, a₁_max⟩ := h g hg
        rcases em (g ∈ X₁) with h₁ | h₁
        · rw [h₁.right] at g_lt_f
          exact Relation.irrefl g_lt_f
        · rcases em (g ∈ X₀) with h₀ | h₀
          · have := hb₀ (g.val a₀) (Set.mem_image' h₀)
            contradiction
          · simp only [Set.mem_inter, hg, Set.ofMem_mem, true_and, LEM.not_forall,
            Decidable.not_not, X₀] at h₀
            obtain ⟨a₁, ⟨b, a₁_mem_gsupp⟩, a₀_lt_a₁⟩ := h₀
            rw [g_eq_f _ a₀_lt_a₁] at a₁_mem_gsupp
            have := f'_mem.left.right _ ⟨_, a₁_mem_gsupp⟩
            contradiction

def pow_rel_map
  [LEM]
  {r₀: α₀ -> α₀ -> Prop} {r₁: α₁ -> α₁ -> Prop}
  {s₀: β₀ -> β₀ -> Prop} {s₁: β₁ -> β₁ -> Prop}
  (hr: r₁ ≃r r₀) (hs: s₀ ≃r s₁) : pow_rel r₀ s₀ →r pow_rel r₁ s₁ where
  toFun f := {
    val a := hs (f.val (hr a))
    property := by
      apply Finite.ofEmbed (β := f.support)
      refine {
        toFun x := {
          val := hr x
          property := by
            obtain ⟨x, hx⟩ := x; dsimp
            simp only [Set.mem_preimage] at hx
            obtain ⟨b, hx⟩ := hx
            rw [←hs.symm_coe b, ←map_rel hs] at hx
            exact ⟨_, hx⟩
        }
        inj := ?_
      }
      intro ⟨a, ha⟩ ⟨b, hb⟩ h; dsimp at h
      ext; dsimp; exact inj hr (Subtype.mk.inj h)
  }
  map_rel {f g} := by
    apply Iff.intro
    · intro ⟨a, sa, ha⟩
      exists hr.symm a
      simp only [RelEquiv.symm_coe, ← map_rel hs, sa, true_and]
      intro x hx
      rw [map_rel hr, RelEquiv.symm_coe] at hx
      congr
      exact ha _ hx
    · intro ⟨a, sa, ha⟩
      exists hr a
      simp only [←map_rel hs] at sa ha
      apply And.intro sa
      intro x hx
      rw [map_rel hr.symm, RelEquiv.coe_symm] at hx
      have := ha _ hx
      simpa only [RelEquiv.symm_coe, (inj hs).eq_iff] using this

def apply_pow_rel_map [LEM] (hr: r₁ ≃r r₀) (hs: s₀ ≃r s₁) (f: pow_ty r₀ s₀) :
  (pow_rel_map hr hs f).val = hs ∘ f.val ∘ hr := rfl

def pow_rel_congr [LEM] (hr: r₀ ≃r r₁) (hs: s₀ ≃r s₁) : pow_rel r₀ s₀ ≃r pow_rel r₁ s₁ where
  toFun := pow_rel_map hr.symm hs
  invFun := pow_rel_map hr hs.symm
  leftInv f := by
    ext; rw [apply_pow_rel_map, apply_pow_rel_map]
    simp only [Function.comp_apply, RelEquiv.symm_coe]
  rightInv f := by
    ext; rw [apply_pow_rel_map, apply_pow_rel_map]
    simp only [Function.comp_apply, RelEquiv.coe_symm]
  map_rel := map_rel _

def pow [LEM] : Ordinal -> Ordinal -> Ordinal :=
  lift₂ (fun r s => type (pow_rel r s)) <| by
    intro _ _ _ _ a b c d _ _ _ _ ac bd
    apply sound
    apply pow_rel_congr
    assumption
    assumption

end Ordinal
