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

public theorem rank_hom_init
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

structure min_ty (r: α -> α -> Prop) (s: β -> β -> Prop) [IsWellOrder r] [IsWellOrder s] where
  left: α
  right: β
  rank_eq: rank_hom r left = rank_hom s right

def min_ty_rel (r: α -> α -> Prop) (s: β -> β -> Prop) [IsWellOrder r] [IsWellOrder s] (x y: min_ty r s) : Prop :=
  r x.left y.left

def min_ty_emb [IsWellOrder r] [IsWellOrder s] : min_ty_rel r s ↪r r where
  toFun := min_ty.left
  map_rel_iff := Iff.rfl
  injective := by
    intro x y h
    suffices x.right = y.right by cases x <;> cases y; congr
    apply (rank_hom s).inj
    rw [←x.rank_eq, ←y.rank_eq, h]

instance [IsWellOrder r] [IsWellOrder s] : IsWellOrder (min_ty_rel r s) :=
  min_ty_emb.liftWellOrder

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
