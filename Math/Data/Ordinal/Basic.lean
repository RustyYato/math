module

public import Math.Data.Ordinal.Defs
public import Math.Order.InitialSeg.Defs

namespace Math.Ordinal

public def le : Ordinal -> Ordinal -> Prop :=
  lift₂ (fun r s => Nonempty (r ≼i s)) <| by
    intro A B C D r s t u _ _ _ _ h g
    simp; apply Iff.intro
    intro ⟨x⟩; refine ⟨RelEquiv.congr_init ?_ ?_ x⟩ <;> assumption
    intro ⟨x⟩; refine ⟨RelEquiv.congr_init ?_ ?_ x⟩ <;> (apply RelEquiv.symm; assumption)

public def lt : Ordinal -> Ordinal -> Prop :=
  lift₂ (fun r s => Nonempty (r ≺i s)) <| by
    intro A B C D r s t u _ _ _ _ h g
    simp; apply Iff.intro
    intro ⟨x⟩; refine ⟨RelEquiv.congr_princ ?_ ?_ x⟩ <;> assumption
    intro ⟨x⟩; refine ⟨RelEquiv.congr_princ ?_ ?_ x⟩ <;> (apply RelEquiv.symm; assumption)

public instance : LE Ordinal where
  le := le
public instance : LT Ordinal where
  lt := lt

@[simp] public theorem type_le_type
  {r: α -> α -> Prop} {s: β -> β -> Prop}
  [IsWellOrder r] [IsWellOrder s] :
  type r ≤ type s ↔ Nonempty (r ≼i s) := by
  apply Iff.of_eq; apply lift₂_type
@[simp] public theorem type_lt_type
  {r: α -> α -> Prop} {s: β -> β -> Prop}
  [IsWellOrder r] [IsWellOrder s] :
  type r < type s ↔ Nonempty (r ≺i s) := by
  apply Iff.of_eq; apply lift₂_type

public instance : IsAntisymm (· ≤ ·: Ordinal -> Ordinal -> Prop) (· = ·) where
  antisymm a b h g := by
    induction a with | @type α r =>
    induction b with | @type β s =>
    simp at h g
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    apply sound
    apply RelEquiv.antisymm <;> assumption

public instance : IsRefl (· ≤ ·: Ordinal -> Ordinal -> Prop) where
  refl a := by
    induction a with | @type α r =>
    apply type_le_type.mpr; refine ⟨?_⟩
    apply InitialSeg.of_eqv
    apply RelEquiv.id

public instance : IsTrans (· ≤ ·: Ordinal -> Ordinal -> Prop) where
  htrans {a b c} h g := by
    induction a with | @type α r =>
    induction b with | @type β s =>
    induction c with | @type γ t =>
    simp at *
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    refine ⟨h.trans g⟩

public instance : IsTrans (· < ·: Ordinal -> Ordinal -> Prop) where
  htrans {a b c} h g := by
    induction a with | @type α r =>
    induction b with | @type β s =>
    induction c with | @type γ t =>
    simp at *
    obtain ⟨h⟩ := h
    obtain ⟨g⟩ := g
    refine ⟨h.trans_init g.toInitialSeg⟩

public instance [LEM] : IsPartialOrder Ordinal where
  lt_iff_le_and_not_ge := by
    intro a b
    induction a with | @type α r =>
    induction b with | @type β s =>
    simp; apply Iff.intro
    intro ⟨f⟩; apply And.intro ⟨f.toInitialSeg⟩
    intro ⟨g⟩
    exact (f.trans_init g).irrefl
    intro ⟨⟨h⟩, g⟩
    replace g := g ∘ Nonempty.intro
    rcases h.eqv_or_principal with hf | hf
    · have (i: β) : exists_unique fun b => h b = i := by
        obtain ⟨a, rfl⟩ := hf i
        refine ⟨a, rfl, ?_⟩
        intro b hb
        exact (Embedding.coe h).inj hb.symm
      replace := Classical.axiomOfUniqueChoice this
      obtain ⟨inv, hinv, inv_uniq⟩ := this
      exfalso; apply g; clear g
      apply InitialSeg.of_eqv
      apply RelEquiv.symm
      exact {
        toRelHom := h.toRelHom
        invFun := inv
        leftInv a := by apply hinv
        rightInv a := by
          apply Embedding.inj (Embedding.coe h)
          apply hinv
      }
    · refine ⟨h.toRelHom, ?_⟩
      obtain ⟨top, htop⟩ := hf
      exists top

variable {A B C D: Type*}

def rank_rel (r: A -> A -> Prop) [IsWellOrder r] (a: A) (x y: { x // r x a }) : Prop := r x y

def rank_rel_init {r: A -> A -> Prop} [IsWellOrder r] {a: A} : rank_rel r a ≼i r where
  toFun := Subtype.val
  map_rel_iff := Iff.rfl
  isInitial := by
    intro ⟨x, hx⟩ b hb
    dsimp at hb
    apply Set.mem_range.mpr
    exists ⟨b, htrans hb hx⟩

def rank_rel_emb (r: A -> A -> Prop) [IsWellOrder r] (a: A) : rank_rel r a ↪r r where
  toRelHom := (rank_rel_init (r := r) (a := a)).toRelHom
  injective := by intro a b h; ext; assumption

instance {r: α -> α -> Prop} [IsWellOrder r] : IsWellOrder (rank_rel r a) :=
  RelEmbedding.liftWellOrder (rank_rel_emb r a)

public def rank (r: A -> A -> Prop) [IsWellOrder r] (a: A) : Ordinal := type (rank_rel r a)

public theorem rank_lt_rank {r: A -> A -> Prop} [IsWellOrder r] :
  r a b -> rank r a < rank r b := by
  intro h
  apply type_lt_type.mpr
  refine ⟨?_⟩
  exact {
    toFun x := {
      val := x.val
      property := htrans x.property h
    }
    map_rel_iff := Iff.rfl
    isPrinciple := by
      exists ⟨a, h⟩
      intro ⟨x, hx⟩
      show r x a ↔ _
      apply Iff.intro
      intro x_lt_a
      refine ⟨⟨x, x_lt_a⟩, ?_⟩
      rfl
      rintro ⟨⟨x, hx⟩, eq⟩
      dsimp at eq; cases eq
      assumption
  }

public theorem of_rank_lt_rank {r: A -> A -> Prop} [IsWellOrder r] :
  rank r a < rank r b -> r a b := by
  intro h; replace ⟨h⟩ := type_lt_type.mp h
  rcases connected (R := r) a b with g | g | g
  assumption; subst b
  nomatch h.irrefl
  replace ⟨g⟩ := type_lt_type.mp (rank_lt_rank g)
  nomatch (h.trans_init g.toInitialSeg).irrefl

public def rank_hom (r: A -> A -> Prop) [IsWellOrder r] : r ↪r (· < ·: Ordinal -> Ordinal -> Prop) where
  toFun := rank r
  map_rel_iff {a b} := by
    apply Iff.intro
    apply rank_lt_rank
    apply of_rank_lt_rank
  injective {a b} eq := by
    rcases connected (R := r) a b with h | h | h
    · have := rank_lt_rank h
      rw [eq] at this
      nomatch irrefl (of_rank_lt_rank this)
    · assumption
    · have := rank_lt_rank h
      rw [eq] at this
      nomatch irrefl (of_rank_lt_rank this)

@[simp] public theorem rank_hom_init
  {A B: Type u} {r: A -> A -> Prop} {s: B -> B -> Prop}
  [IsWellOrder r] [IsWellOrder s]
  (f: r ≼i s) (top: A) : rank_hom s (f top) = rank_hom r top := by
  have (b: { x // s x (f top) }) : exists_unique fun a: { x // r x top } => f a = b := by
    obtain ⟨b, htop⟩ := b
    obtain ⟨i, rfl⟩  := f.isInitial _ _ htop
    dsimp
    exists ⟨i, ?_⟩
    exact map_rel_rev _ htop
    apply And.intro rfl
    dsimp; intro ⟨j, hj⟩ h
    congr; exact Embedding.inj (Embedding.coe f) h.symm
  replace := Classical.axiomOfUniqueChoice this
  obtain ⟨inv, hinv, inv_uniq⟩ := this
  clear inv_uniq; symm; apply sound
  exact {
    toFun x := {
      val := f x.val
      property := map_rel f x.property
    }
    invFun x := inv x
    map_rel_iff := map_rel_iff f
    leftInv a := by dsimp; congr; rw [hinv]
    rightInv a := by
      dsimp; ext; apply Embedding.inj (Embedding.coe f)
      apply hinv
  }

@[simp] public theorem rank_hom_eqv
  {A B: Type u} {r: A -> A -> Prop} {s: B -> B -> Prop}
  [IsWellOrder r] [IsWellOrder s]
  (f: r ≃r s) (top: A) : rank_hom s (f top) = rank_hom r top := by
  show rank_hom s (InitialSeg.of_eqv f top) = _
  rw [rank_hom_init]

public theorem rank_lt_type (r: A -> A -> Prop) [IsWellOrder r] (a: A) : rank r a < type r := by
  apply type_lt_type.mpr
  refine ⟨?_⟩
  exact {
    toFun := Subtype.val
    map_rel_iff := Iff.rfl
    isPrinciple := by
      exists a; intro b
      apply Iff.intro
      intro h; exact ⟨⟨b, h⟩, rfl⟩
      rintro ⟨b, rfl⟩; exact b.property
  }

public theorem lt_type_iff (r: A -> A -> Prop) [IsWellOrder r] (o: Ordinal) : o < type r ↔ o ∈ Set.range (rank_hom r) := by
  induction o with | @type B s =>
  apply Iff.intro
  · intro f; replace ⟨f⟩ := type_lt_type.mp f
    have ⟨top, htop⟩ := f.isPrinciple
    have := (htop ·)
    have (x: { x // r x top }) : exists_unique fun a => f a = x := by
      have ⟨a, ha⟩ := (this x.val).mp x.property
      exists a; apply And.intro ha
      intro b hb
      apply Embedding.inj (Embedding.coe f.toInitialSeg)
      exact ha.trans hb.symm
    replace := Classical.axiomOfUniqueChoice this
    obtain ⟨inv, hinv, h⟩ := this; clear h
    exists top; symm; apply sound
    exact {
      toFun x := {
        val := f x
        property := by
          apply (htop _).mpr
          apply Set.mem_range'
      }
      invFun := inv
      leftInv x := by dsimp; congr; rw [hinv]
      rightInv x := by
        apply Embedding.inj (Embedding.coe f.toInitialSeg)
        apply hinv
      map_rel_iff {a b} := map_rel_iff f
    }
  · intro ⟨a, ha⟩; rw [←ha]; clear ha
    apply rank_lt_type

public instance : IsWelFounded (· < ·: Ordinal -> Ordinal -> Prop) where
  wf := by
    apply WellFounded.intro
    intro a
    induction a with | @type α r =>
    apply Acc.intro
    intro _ h; rw [lt_type_iff] at h
    obtain ⟨a, rfl⟩ := h
    induction a using (wf (R := r)).induction with
    | _ a ih =>
    apply Acc.intro
    intro b h
    obtain ⟨b, rfl⟩ := (lt_type_iff r _).mp (htrans h (rank_lt_type r a))
    apply ih; apply of_rank_lt_rank
    assumption

section

variable {α β: Type u}
  (r: α -> α -> Prop) (s: β -> β -> Prop)
  [IsWellOrder r] [IsWellOrder s]
  (r': α' -> α' -> Prop) (s': β' -> β' -> Prop)
  [IsWellOrder r'] [IsWellOrder s']

public instance : IsWellOrder (Sum.Lex r s) where
  htrans := by
    intro a b c h g
    cases h <;> cases g
    apply Sum.Lex.inl; apply htrans <;> assumption
    apply Sum.Lex.sep
    apply Sum.Lex.inr; apply htrans <;> assumption
    apply Sum.Lex.sep
  connected {a b} := by
    cases a <;> cases b
    · rename_i a b
      rcases connected (R := r) a b with h | h | h
      · left; apply Sum.Lex.inl; assumption
      · right; left; congr
      · right; right; apply Sum.Lex.inl; assumption
    · left; apply Sum.Lex.sep
    · right; right; apply Sum.Lex.sep
    · rename_i a b
      rcases connected (R := s) a b with h | h | h
      · left; apply Sum.Lex.inr; assumption
      · right; left; congr
      · right; right; apply Sum.Lex.inr; assumption
  wf := by
    apply WellFounded.intro
    suffices ∀a: α, Acc (Sum.Lex r s) (.inl a) by
      intro a; cases a with
      | inl a => apply this
      | inr a =>
      induction a using (wf (R := s)).induction with
      | _ a ih =>
      apply Acc.intro
      intro b h; cases h
      apply ih; assumption
      apply this
    intro a
    induction a using (wf (R := r)).induction with
    | _ a ih =>
    apply Acc.intro
    intro b h; cases h
    apply ih; assumption

def map_lex (fr: r ≃r r') (fs: s ≃r s') : Sum.Lex r s ≼i Sum.Lex r' s' where
  toFun
  | .inl x => .inl (fr x)
  | .inr x => .inr (fs x)
  map_rel_iff := by
    intro a b
    cases a <;> cases b <;> simp
    · apply map_rel_iff fr
    · apply map_rel_iff fs
  isInitial := by
    intro a b  h
    dsimp at h
    cases a <;> cases h
    rename_i x _
    exists .inl (fr.symm x); simp
    rename_i x _
    exists .inr (fs.symm x); simp
    rename_i x
    exists .inl (fr.symm x); simp

public def add : Ordinal.{u} -> Ordinal.{u} -> Ordinal.{u} :=
  lift₂ (fun a b => type (Sum.Lex a b)) <| by
    intro _ _ _ _ r s r' s' _ _ _ _ h g
    apply sound; apply RelEquiv.antisymm
    apply map_lex <;> assumption
    apply map_lex <;> (apply RelEquiv.symm; assumption)

public instance : Add Ordinal where
  add := add

@[simp] public theorem type_add_type : type r + type s = type (Sum.Lex r s) := by
  apply lift₂_type

public theorem left_le_add (a b: Ordinal) : a ≤ a + b := by
  induction a with | @type A r =>
  induction b with | @type B s =>
  simp; refine ⟨?_⟩
  exact {
    toFun := .inl
    map_rel_iff {a b} := by
      apply Iff.intro
      apply Sum.Lex.inl
      intro h; cases h
      assumption
    isInitial := by
      intro a b h; cases h
      apply Set.mem_range'
  }

public theorem right_le_add [LEM] (a b: Ordinal) : b ≤ a + b := by
  induction a with | @type A r =>
  induction b with | @type B s =>
  simp; refine ⟨?_⟩
  apply InitialSeg.collapse
  exact {
    toFun := .inr
    injective {_ _} := Sum.inr.inj
    map_rel_iff := by
      intro a b
      apply Iff.intro
      apply Sum.Lex.inr
      intro h; cases h; assumption
  }

public instance [LEM] : IsWellOrder (· < ·: Ordinal -> Ordinal -> Prop) where
  connected a b := by
    have ⟨o, a_le_o, b_le_o⟩ : ∃o, a ≤ o ∧ b ≤ o := ⟨a + b, left_le_add _ _, right_le_add _ _⟩
    rcases lt_or_eq_of_le a_le_o with a_lt_o | rfl <;>
    rcases lt_or_eq_of_le b_le_o with b_lt_o | rfl
    · induction o with | type r =>
      rw [lt_type_iff] at a_lt_o b_lt_o
      obtain ⟨a, rfl⟩ := a_lt_o
      obtain ⟨b, rfl⟩ := b_lt_o
      simp [←map_rel_iff (rank_hom r), (rank_hom r).inj.eq_iff]
      apply connected
    · left; assumption
    · right; right ;assumption
    · right; left; rfl

public instance [LEM] : IsLinearOrder Ordinal where

end

structure min_ty (r: α -> α -> Prop) (s: β -> β -> Prop) [IsWellOrder r] [IsWellOrder s] where
  left: α
  right: β
  rank_eq: rank_hom r left = rank_hom s right

def min_ty_rel (r: α -> α -> Prop) (s: β -> β -> Prop) [IsWellOrder r] [IsWellOrder s] (x y: min_ty r s) : Prop :=
  r x.left y.left

def min_ty_emb_left [IsWellOrder r] [IsWellOrder s] : min_ty_rel r s ↪r r where
  toFun := min_ty.left
  map_rel_iff := Iff.rfl
  injective := by
    intro x y h
    suffices x.right = y.right by cases x <;> cases y; congr
    apply (rank_hom s).inj
    rw [←x.rank_eq, ←y.rank_eq, h]

def min_ty_emb_right [IsWellOrder r] [IsWellOrder s] : min_ty_rel r s ↪r s where
  toFun := min_ty.right
  map_rel_iff {a b} := by
    show r a.left b.left ↔ _
    rw [map_rel_iff (rank_hom r), a.rank_eq, b.rank_eq,
      ←map_rel_iff (rank_hom s)]
  injective := by
    intro x y h
    suffices x.left = y.left by cases x <;> cases y; congr
    apply (rank_hom r).inj
    rw [x.rank_eq, y.rank_eq, h]

instance [IsWellOrder r] [IsWellOrder s] : IsWellOrder (min_ty_rel r s) :=
  min_ty_emb_left.liftWellOrder

def min_helper
  [IsWellOrder r₀] [IsWellOrder s₀]
  [IsWellOrder r₁] [IsWellOrder s₁]
  (h: r₀ ≃r r₁) (g: s₀ ≃r s₁) :
  min_ty_rel r₀ s₀ ≼i min_ty_rel r₁ s₁ where
  toFun x := {
    left := h x.left
    right := g x.right
    rank_eq := by
      show rank_hom r₁ (InitialSeg.of_eqv h x.left) = rank_hom s₁ (InitialSeg.of_eqv g x.right)
      rw [rank_hom_init, rank_hom_init]
      exact x.rank_eq
  }
  map_rel_iff {a b} := map_rel_iff h
  isInitial := by
    intro a b
    show r₁ _ _ -> _; dsimp
    intro hr
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    exact h.symm b.left
    exact g.symm b.right
    show rank_hom _ (InitialSeg.of_eqv h.symm b.left) = rank_hom _ (InitialSeg.of_eqv g.symm b.right)
    rw [rank_hom_init, rank_hom_init]
    exact b.rank_eq
    simp

public def min : Ordinal.{u} -> Ordinal.{u} -> Ordinal.{u} :=
  lift₂ (fun r s => type (min_ty_rel r s)) <| by
    intro A B C D r₀ s₀ r₁ s₁ _ _ _ _ h g
    apply sound; apply RelEquiv.antisymm
    apply min_helper <;> assumption
    apply min_helper <;> (apply RelEquiv.symm; assumption)

section

variable {α β α' β': Type u}
  (r: α -> α -> Prop) (s: β -> β -> Prop) [IsWellOrder r] [IsWellOrder s]
  (r': α' -> α' -> Prop) (s': β' -> β' -> Prop) [IsWellOrder r'] [IsWellOrder s']

def max_ty_get : α ⊕ β -> Ordinal
| .inl x => rank_hom r x
| .inr x => rank_hom s x

def max_setoid
  (r: α -> α -> Prop) (s: β -> β -> Prop)
  [IsWellOrder r] [IsWellOrder s]
  : Setoid (α ⊕ β) := setoid (fun a b => max_ty_get r s a = max_ty_get r s b)

def max_ty :=
  Quotient (max_setoid r s)

def max_ty.get : max_ty r s -> Ordinal :=
  Quotient.lift (max_ty_get r s) <| by
    intros; assumption

def max_ty_rel (x y: max_ty r s) : Prop :=
  x.get < y.get

def max_ty_hom : max_ty_rel r s ↪r (· < ·: Ordinal.{u} -> Ordinal -> Prop) where
  toFun x := x.get
  map_rel_iff := Iff.rfl
  injective := by
    intro a b h; dsimp at h
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    apply Quotient.sound; assumption

instance [LEM] : IsWellOrder (max_ty_rel r s) :=
  (max_ty_hom r s).liftWellOrder

def map_max_ty (h: r ≃r r') (g: s ≃r s') : max_ty_rel r s ≼i max_ty_rel r' s' where
  toFun :=
    Quotient.lift (fun x => Quotient.mk _ (x.map h g)) <| by
      intro x y hx; apply Quotient.sound
      cases x <;> cases y <;> dsimp
      show rank_hom _ (InitialSeg.of_eqv h _) = rank_hom _ (InitialSeg.of_eqv h _)
      rwa [rank_hom_init, rank_hom_init]
      show rank_hom _ (InitialSeg.of_eqv g _) = rank_hom _ (InitialSeg.of_eqv h _)
      rwa [rank_hom_init, rank_hom_init]
      show rank_hom _ (InitialSeg.of_eqv h _) = rank_hom _ (InitialSeg.of_eqv g _)
      rwa [rank_hom_init, rank_hom_init]
      show rank_hom _ (InitialSeg.of_eqv g _) = rank_hom _ (InitialSeg.of_eqv g _)
      rwa [rank_hom_init, rank_hom_init]
  map_rel_iff {a b} := by
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    cases a <;> cases b
    all_goals
      apply Iff.intro
      intro hx
      show rank_hom _ _ < rank_hom _ _
    any_goals simpa
    all_goals
      intro hx
      replace hx : rank_hom _ _ < rank_hom _ _ := hx
      simp at hx
      assumption
  isInitial := by
    intro a b hx
    induction a using Quotient.ind with | _ a =>
    induction b using Quotient.ind with | _ b =>
    cases a <;> cases b
    all_goals
      replace hx : rank_hom _ _ < rank_hom _ _ := hx
      simp at hx
    rw [←rank_hom_eqv h, ←map_rel_iff (rank_hom _)] at hx
    · rename_i a a'
      rw [←h.symm_apply a']
      exists Quotient.mk _ (Sum.inl (h.symm a'))
    · rename_i a a'
      exists Quotient.mk _ (Sum.inr (g.symm a'))
      apply Quotient.sound
      simp; rfl
    · rename_i a a'
      rw [←h.symm_apply a']
      exists Quotient.mk _ (Sum.inl (h.symm a'))
    · rename_i a a'
      rw [←g.symm_apply a']
      exists Quotient.mk _ (Sum.inr (g.symm a'))

public def max [LEM] : Ordinal.{u} -> Ordinal.{u} -> Ordinal.{u} :=
  lift₂ (fun r s => type (max_ty_rel r s)) <| by
    intro A B C D r s r' s' _ _ _ _ h g
    apply sound; apply RelEquiv.antisymm
    apply map_max_ty <;> assumption
    apply map_max_ty <;> (apply RelEquiv.symm; assumption)

public instance : Min Ordinal where
  min := min

public instance [LEM] : Max Ordinal where
  max := max

theorem type_min_type : (type r) ⊓ (type s) = type (min_ty_rel r s) := by apply lift₂_type
theorem type_max_type [LEM] : (type r) ⊔ (type s) = type (max_ty_rel r s) := by apply lift₂_type

end

@[simp] theorem quotient_lift_mk (f: α -> β) hf a : Quotient.lift f hf (Quotient.mk s a) = f a := rfl

public instance [LEM] : IsLattice Ordinal.{u} where
  left_le_max a b := by
    induction a with | _ r =>
    induction b with | _ s =>
    rw [type_max_type]; apply type_le_type.mpr
    refine ⟨?_⟩; apply InitialSeg.collapse
    exact {
      toFun a := Quotient.mk _ (.inl a)
      map_rel_iff := map_rel_iff (rank_hom r)
      injective := by
        intro a b h; dsimp at h
        exact (rank_hom r).inj (Quotient.exact h)
    }
  right_le_max a b := by
    induction a with | _ r =>
    induction b with | _ s =>
    rw [type_max_type]; apply type_le_type.mpr
    refine ⟨?_⟩; apply InitialSeg.collapse
    exact {
      toFun a := Quotient.mk _ (.inr a)
      map_rel_iff := map_rel_iff (rank_hom s)
      injective := by
        intro a b h; dsimp at h
        exact (rank_hom s).inj (Quotient.exact h)
    }
  max_le {k a b} := by
    induction a with | @type A r =>
    induction b with | @type B s =>
    induction k with | @type K t =>
    simp [type_max_type]
    intro ⟨fr⟩ ⟨fs⟩; refine ⟨?_⟩; apply InitialSeg.collapse
    exact {
      toFun := Quotient.lift (fun x => x.elim fr fs) <| by
        intro a b h
        cases a <;> cases b <;> dsimp
        all_goals
        apply (rank_hom t).inj
        simpa
      map_rel_iff {a b} := by
        induction a using Quotient.ind with | _ a =>
        induction b using Quotient.ind with | _ b =>
        cases a <;> cases b
        all_goals show rank_hom _ _ < rank_hom _ _ ↔ t _ _; dsimp
        all_goals
          apply Iff.trans _ (map_rel_iff (rank_hom _)).symm
          simp
      injective := by
        intro a b h
        induction a using Quotient.ind with | _ a =>
        induction b using Quotient.ind with | _ b =>
        apply Quotient.sound
        cases a <;> cases b
        all_goals
          simp at h
          show rank_hom _ _ = rank_hom _ _
          iterate 2 first|rw [←rank_hom_init fr]|rw [←rank_hom_init fs]
          rw [h]
    }
  min_le_left a b := by
    induction a with | @type A r =>
    induction b with | @type B s =>
    rw [type_min_type]; apply type_le_type.mpr
    exact ⟨InitialSeg.collapse min_ty_emb_left⟩
  min_le_right a b := by
    induction a with | @type A r =>
    induction b with | @type B s =>
    rw [type_min_type]; apply type_le_type.mpr
    exact ⟨InitialSeg.collapse min_ty_emb_right⟩
  le_min {k a b} := by
    induction a with | @type A r =>
    induction b with | @type B s =>
    induction k with | @type K t =>
    simp [type_min_type]
    intro ⟨fr⟩ ⟨fs⟩; refine ⟨?_⟩; apply InitialSeg.collapse
    exact {
      toFun k := {
        left := fr k
        right := fs k
        rank_eq := by simp
      }
      map_rel_iff {a b} := by
        show _ ↔ r _ _; simp
        rw [map_rel_iff (rank_hom r)]
        simp [map_rel_iff (rank_hom t)]
      injective {a b} h := by
        dsimp at h
        exact (Embedding.coe fr).inj (min_ty.mk.inj h).left
    }
