module

public import Math.Data.Equiv.Basic
public import Math.Data.Embedding.Basic
public import Math.Data.Cardinal.Defs
public import Math.Order.InitialSeg.Defs
public import Math.Order.Defs
import Math.Data.List.Defs

namespace Math.Cardinal

public def le : Cardinal -> Cardinal -> Prop :=
  lift₂ (fun a b => Nonempty (a ↪ b)) <| by
    intro A B C D h g
    simp; apply Iff.intro
    intro ⟨f⟩; exact ⟨Equiv.congr_embedding h g f⟩
    intro ⟨f⟩; exact ⟨Equiv.congr_embedding h.symm g.symm f⟩

public instance : LE Cardinal where
  le := le
public instance : LT Cardinal where
  lt a b := a ≤ b ∧ ¬b ≤ a

public theorem type_le_type : A ↪ B -> type A ≤ type B := by
  intro f; show le _ _; unfold le
  rw [lift₂_type]
  exact ⟨f⟩
public theorem of_type_le_type : type A ≤ type B -> Nonempty (A ↪ B) := by
  show le _ _ -> _; unfold le
  rw [lift₂_type]
  exact id

public theorem type_le_type_iff : type A ≤ type B ↔ Nonempty (A ↪ B) := by
  apply Iff.intro of_type_le_type
  intro ⟨f⟩; exact type_le_type f

public instance : IsPreorder Cardinal where
  lt_iff_le_and_not_ge := Iff.rfl
  refl a := by
    induction a; apply type_le_type
    exact .id _
  htrans {A B C} h g := by
    induction A with | _ A =>
    induction B with | _ B =>
    induction C with | _ C =>
    replace ⟨h⟩ := of_type_le_type h
    replace ⟨g⟩ := of_type_le_type g
    apply type_le_type
    exact h.trans g

public def fin : ℕ →o Cardinal where
  toFun n := type (Fin n)
  map_rel_iff {n m} := by
    apply Iff.trans _ type_le_type_iff.symm
    apply Iff.intro
    intro h; exact ⟨Embedding.fin h⟩
    intro ⟨h⟩; exact Embedding.of_fin h

def erase_missing (f: α ↪ Fin (n + 1)) (i: Fin (n + 1)) (hi: i ∉ Set.range f) : α ↪ Fin n where
  toFun a :=
    let j := f a
    if h:j.val < i.val then ⟨j, by omega⟩ else ⟨j.val - 1, by
      have : j.val ≠ i.val := by
        simp [Fin.val_inj]; intro rfl
        exact hi Set.mem_range'
      omega⟩
  injective := by
    intro a b h; dsimp at h
    have : (f a).val ≠ i.val := by
        simp [Fin.val_inj]; intro rfl
        exact hi Set.mem_range'
    have : (f b).val ≠ i.val := by
      simp [Fin.val_inj]; intro rfl
      exact hi Set.mem_range'
    split at h <;> split at h <;> rename_i h₀ h₁
    · simpa [Fin.val_inj, f.inj.eq_iff] using h
    · simp at h₀ h
      have : f a = i.val := by omega
      contradiction
    · simp at h₀ h
      have : f a = i.val := by omega
      contradiction
    · simp at h
      replace h := Nat.pred_inj ?_ ?_ h
      simpa [Fin.val_inj, f.inj.eq_iff] using h
      simp; omega
      simp; omega

@[expose] public def fin' [LEM] : ℕ ≼i Cardinal where
  toRelHom := fin
  isInitial := by
    intro n c h
    show c ∈ Set.range fin
    replace h : c ≤ fin n := h
    induction c with | _ α =>
    have _ := instIsWelFoundedNatLt
    have ⟨c, ⟨f⟩, hf⟩ := exists_min (P := fun n: Nat => Nonempty (α ↪ Fin n)) (· < ·) ⟨_, of_type_le_type h⟩
    have (i: Fin c) : exists_unique fun a => i = f a := by
      rcases em (∃(n: ℕ) (as: Fin n -> α), ∀a, a ∈ Set.range as) with ha | ha
      · obtain ⟨k, g, hg⟩ := ha
        have ⟨j, hj⟩ : ∃j: Fin k, f (g j) = i := ?_
        exists g j; dsimp
        apply And.intro hj.symm
        intro a rfl
        exact f.inj hj
        apply LEM.byContradiction
        intro h; simp at h
        cases c with
        | zero => exact i.elim0
        | succ c =>
          have := erase_missing f i ?_
          exact hf _ ⟨this⟩ (Nat.lt_succ_self _)
          simp only [Set.mem_range, not_exists]; intro a ha
          have := hg a
          simp only [Set.mem_range] at this
          obtain ⟨j, rfl⟩ := this
          exact h _ ha
      · simp only [Set.mem_range, not_exists, LEM.not_forall] at ha
        have ⟨as, as_len, as_nodup⟩ : ∃as: List α, c < as.length ∧ as.Nodup := by
          clear f hf i
          induction c with
          | zero =>
            have ⟨a, h⟩ := ha 0 elim_empty
            refine ⟨[a], Nat.zero_lt_succ _, ?_⟩
            simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
              and_self]
          | succ c ih =>
            obtain ⟨as, as_len, as_nodup⟩ := ih
            have ⟨a, ha⟩ := ha as.length (fun i => as[i])
            refine ⟨a::as, ?_, ?_⟩
            apply Nat.succ_lt_succ; assumption
            apply List.nodup_cons.mpr
            apply And.intro _ as_nodup
            rw [List.mem_iff_getElem]
            intro ⟨j, hj, eq⟩
            exact ha ⟨_, hj⟩ eq
        have := List.nodup_map f f.inj as as_nodup
        rw [←List.length_map f] at as_len

        have f' : Fin (List.map f as).length ↪ Fin c := {
          toFun i := (List.map f as)[i]
          injective := by
            intro i j h; ext
            exact (List.nodup_iff_eq_of_getElem_eq.mp this) i j i.isLt j.isLt h
        }
        nomatch Nat.not_le_of_lt as_len (Embedding.of_fin f')
    replace ⟨finv, linv, _⟩ := Classical.axiomOfUniqueChoice this
    dsimp at *
    simp only [Set.mem_range]; exists c
    symm; apply sound
    refine {
      toFun := f
      invFun := finv
      leftInv := ?_
      rightInv := ?_
    }
    · intro i; rw [←linv]
    · intro a; apply f.inj
      rw [←linv]

public def ulift : Cardinal.{u} →o Cardinal.{max u v} where
  toFun := lift (fun A => type (ULift A)) <| by
    intro A B h; apply sound
    exact Equiv.congr_ulift h
  map_rel_iff {A B} := by
    induction A with | _ A =>
    induction B with | _ B =>
    rw [lift_type, lift_type]
    apply Iff.trans type_le_type_iff
    apply Iff.trans _ type_le_type_iff.symm
    apply Iff.intro
    intro ⟨f⟩; refine ⟨?_⟩
    exact (Equiv.congr_embedding Equiv.ulift Equiv.ulift).symm f
    intro ⟨f⟩; refine ⟨?_⟩
    exact Equiv.congr_embedding Equiv.ulift Equiv.ulift f

-- public def ulift' : Cardinal.{u} ≼i Cardinal.{max u v} where
--   toRelHom := ulift
--   isInitial := by
--     unfold ulift; dsimp; intro A B h
--     induction A with | _ A =>
--     induction B with | _ B =>
--     rw [lift_type] at h
--     replace ⟨h⟩ := of_type_le_type h
--     sorry

public def plift : Cardinal.{u} →o Cardinal.{u + 1} where
  toFun := lift (fun A => type (PLift A)) <| by
    intro A B h; apply sound
    exact Equiv.congr_plift h
  map_rel_iff {A B} := by
    induction A with | _ A =>
    induction B with | _ B =>
    rw [lift_type, lift_type]
    apply Iff.trans type_le_type_iff
    apply Iff.trans _ type_le_type_iff.symm
    apply Iff.intro
    intro ⟨f⟩; refine ⟨?_⟩
    exact (Equiv.congr_embedding Equiv.plift Equiv.plift).symm f
    intro ⟨f⟩; refine ⟨?_⟩
    exact Equiv.congr_embedding Equiv.plift Equiv.plift f
