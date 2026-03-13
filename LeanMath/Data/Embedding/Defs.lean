import LeanMath.Logic.Funlike
import LeanMath.Logic.Nontrivial
import LeanMath.Logic.IsEmpty

structure Embedding (α β: Sort*) where
  toFun: α -> β
  protected inj: Function.Injective toFun

infixr:50 " ↪ " => Embedding

class EmbeddingLike (F: Sort*) (α β: outParam Sort*) where
  protected coeEmbedding : F -> α ↪ β := by intro f; exact f.toEmbedding
  protected coeInj : Function.Injective coeEmbedding := by
    intro a b h
    cases a; cases b
    dsimp at h
    congr
    try
      apply EmbeddingLike.coeInj
      assumption

--- This is not the interface for ops, just ensures that
--- all ops are implemented
set_option checkBinderAnnotations false in
class EmbeddingOpsCheck (C: Sort u -> Sort u) (F: ∀α β, C α -> C β -> Sort v)
  [∀α β [cα: C α] [cβ: C β], EmbeddingLike (F α β cα cβ) α β]
  where
  protected comp {α β γ: Sort u} [cα: C α] [cβ: C β] [cγ: C γ] : F β γ cβ cγ -> F α β cα cβ -> F α γ cα cγ
  protected trans {α β γ: Sort u} [cα: C α] [cβ: C β] [cγ: C γ] : F α β cα cβ -> F β γ cβ cγ -> F α γ cα cγ
  protected refl (α: Sort u) [cα: C α] : F α α cα cα

instance {F α β: Sort*} [EmbeddingLike F α β] : FunLike F α β where
  coeFun f := (EmbeddingLike.coeEmbedding (F := F) f).toFun
  coeInj := by
    intro a b h
    suffices EmbeddingLike.coeEmbedding a = EmbeddingLike.coeEmbedding b by
      exact EmbeddingLike.coeInj this
    dsimp at h
    revert h;
    generalize EmbeddingLike.coeEmbedding a = a
    generalize EmbeddingLike.coeEmbedding b = b
    intro h
    cases a; cases b; congr

instance : EmbeddingLike (α ↪ β) α β where
  coeEmbedding := id

def inj [EmbeddingLike F α β] (f: F) : Function.Injective f := by
  intro a b h
  have : EmbeddingLike.coeEmbedding f a = EmbeddingLike.coeEmbedding f b := h
  exact Embedding.inj _ this

namespace Embedding

protected def id (α: Sort*) : α ↪ α where
  toFun := id
  inj _ _ := id

def comp (f: β ↪ γ) (g: α ↪ β) : α ↪ γ where
  toFun := f ∘ g
  inj _ _ h := g.inj (f.inj h)

abbrev trans (f: α ↪ β) (g: β ↪ γ) : α ↪ γ := g.comp f

@[simp] def apply_toFun (f: α ↪ β) (x: α) : f.toFun x = f x := rfl

@[simp] def apply_id (α: Sort*) (x: α) : Embedding.id α x = x := rfl
@[simp] def apply_comp (f: β ↪ γ) (g: α ↪ β) (x: α) : (f.comp g) x = f (g x) := rfl
@[simp] def apply_trans (f: β ↪ γ) (g: α ↪ β) (x: α) : (g.trans f) x = f (g x) := rfl

def swap [DecidableEq α] (i j: α) (f: α ↪ β) : α ↪ β where
  toFun a := if a = i then f j else if a = j then f i else f a
  inj := by
    intro a b h
    dsimp at h; split at h; subst a; split at h
    subst i; rfl
    split at h; subst b
    exact f.inj h.symm
    cases f.inj h
    contradiction
    split at h; subst a; split at h
    cases f.inj h
    contradiction
    split at h
    symm; assumption
    cases f.inj h
    contradiction
    split at h
    cases f.inj h
    contradiction
    split at h
    cases f.inj h
    contradiction
    exact f.inj h

def apply_swap [DecidableEq α] (i j a: α) (f: α ↪ β) : f.swap i j a = if a = i then f j else if a = j then f i else f a := rfl

def fin_val : Fin n ↪ ℕ where
  toFun := Fin.val
  inj _ _ := Fin.val_inj.mp

def fin_of_le (h: n ≤ m) : Fin n ↪ Fin m where
  toFun := Fin.castLE h
  inj := by
    intro a b h
    simp [←Fin.val_inj] at h
    simpa [Fin.val_inj] using h

def le_of_fin (f: Fin n ↪ Fin m) : n ≤ m := by
  induction n generalizing m with
  | zero => apply Nat.zero_le
  | succ n ih =>
    cases m with
    | zero => exact (f 0).elim0
    | succ m =>
    apply Nat.succ_le_succ
    apply ih
    have lt_of_ne (i: Fin (n + 1)) (hi: f i ≠ Fin.last _) : f i < m := by
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp (f i).isLt) with h | h
      assumption; simp at hi
      rw [←Fin.val_inj, h] at hi
      contradiction
    have castSucc_ne_last (i: Fin n) : i.castSucc ≠ Fin.last _ := by
      intro hi
      have : i.castSucc < n := by simp
      rw [hi] at this
      exact Nat.lt_irrefl _ this
    by_cases hf:f (Fin.last _) = Fin.last _
    refine {
      toFun i :=  {
        val := f i.castSucc
        isLt := ?_
      }
      inj := ?_
    }
    · rcases Nat.lt_or_eq_of_le (f i.castSucc).isLt with h | h
      apply Nat.lt_of_succ_lt_succ
      assumption
      simp [←Fin.val_inj, ←Nat.succ.inj h] at hf
      have := castSucc_ne_last _ (f.inj (Fin.val_inj.mp hf)).symm
      contradiction
    · intro a b h; dsimp at h
      simp [Fin.val_inj] at h
      simpa [Fin.castSucc_inj] using f.inj h
    refine {
      toFun i := {
        val :=
          let v := f i.castSucc
          if v = Fin.last _ then
            f (Fin.last _)
          else
            v
        isLt := ?_
      }
      inj := ?_
    }
    · dsimp
      split
      apply lt_of_ne
      assumption
      apply lt_of_ne
      assumption
    · intro a b h
      simp at h
      split at h <;> split at h
      rename_i h₀ h₁; rw [←h₁] at h₀
      simpa [Fin.castSucc_inj] using f.inj h₀
      replace h := f.inj (Fin.val_inj.mp h)
      have := castSucc_ne_last _ h.symm
      contradiction
      replace h := f.inj (Fin.val_inj.mp h)
      have := castSucc_ne_last _ h
      contradiction
      simpa [Fin.val_inj, (inj f).eq_iff, Fin.castSucc_inj] using h

def empty [IsEmpty α] : α ↪ β where
  toFun := elim_empty
  inj := rec_elim_empty

def subtype_val {P: α -> Prop} : { x // P x } ↪ α where
  toFun := Subtype.val
  inj a b h := by
    obtain ⟨a, h⟩ := a
    obtain ⟨b, h⟩ := b
    congr

def cantor [h: Nontrivial β] (f: (α -> β) ↪ α) : False := by
  classical
  have ⟨default, _, _⟩ := h
  let f' (a: α) : β :=
    if hg:∃g, f g = a then
      Classical.choose (Nontrivial.exists_ne (Classical.choose hg a))
    else
      default
  have : f' (f f') ≠ f' (f f') := by
    conv => { lhs; arg 0; simp [f'] }
    have spec : ∃g, f g = f f' := ⟨_, rfl⟩
    rw [dif_pos spec]
    let f₀ := Classical.choose spec
    let spec': ∃ b, f₀ (f f') ≠ b := Nontrivial.exists_ne (f₀ (f f'))
    show Classical.choose spec' ≠ f' (f f')
    have := Classical.choose_spec spec'
    suffices h₀:f₀ = f' by
      rw [show f' (f f') = f₀ (f f') by rw [←h₀]]
      exact this.symm
    apply inj f
    show f f₀ = f f'
    apply Classical.choose_spec spec
  contradiction

end Embedding
