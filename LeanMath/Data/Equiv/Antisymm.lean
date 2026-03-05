import LeanMath.Data.Set.Defs
import LeanMath.Data.Equiv.Defs

variable {α: Type u} {β: Type v} (f: α ↪ β) (g: β ↪ α)

private def preCset : Nat -> Set α
| 0 => (Set.range g)ᶜ
| n + 1 => (preCset n).image (g ∘ f)

private def Cset : Set α := Set.iSup (fun i: ℕ => preCset f g i)

private def mem_range_g (h: a ∉ Cset f g) : ∃b, a = g b := by
  unfold Cset at h
  simp at h
  replace h := h 0
  simp [preCset] at h
  assumption

def mem_Cset_image (h: a ∈ Cset f g) : g (f a) ∈ Cset f g := by
  simp [Cset] at *
  obtain ⟨i, hi⟩ := h
  exists i + 1
  apply Set.mem_image'
  assumption

private noncomputable def bij (f: α ↪ β) (g: β ↪ α) (a: α) : β :=
  open Classical in
  if h:a ∈ Cset f g then
    f a
  else
    Classical.choose (mem_range_g f g h)

def cantor_bernstein_schröder : Nonempty (α ↭ β) := by
  let C := Set.iSup (fun i: ℕ => preCset f g i)
  refine ⟨bij f g, ?_, ?_⟩
  · intro a₀ a₁ h
    unfold bij at h
    split at h <;> split at h <;> rename_i h₀ h₁
    · exact f.inj h
    · exfalso
      have := Classical.choose_spec (mem_range_g _ _ h₁)
      rw [←h] at this
      clear h
      rw [this] at h₁
      apply h₁
      apply mem_Cset_image
      assumption
    · exfalso
      have := Classical.choose_spec (mem_range_g _ _ h₀)
      rw [h] at this
      clear h
      rw [this] at h₀
      apply h₀
      apply mem_Cset_image
      assumption
    · have g₀ := Classical.choose_spec (mem_range_g _ _ h₀)
      have g₁ := Classical.choose_spec (mem_range_g _ _ h₁)
      rwa [h, ←g₁] at g₀
  · intro b
    let a := g b
    by_cases h:a ∈ Cset f g
    · simp [Cset] at h
      obtain ⟨i, hi⟩ := h
      cases i with
      | zero =>
        simp [preCset] at hi
        nomatch hi b rfl
      | succ i =>
        simp [preCset] at hi
        obtain ⟨a', ha', h⟩ := hi
        cases inj g h
        clear a h
        exists a'
        unfold bij
        rw [dif_pos]
        simp [Cset]
        exists i
    · exists a
      unfold bij
      rw [dif_neg h]
      apply inj g
      rw [←Classical.choose_spec (mem_range_g _ _ h)]

noncomputable def Equiv.antisymm : α ≃ β := Classical.choice <| by
  have ⟨f⟩ := cantor_bernstein_schröder f g
  have ⟨g, hg⟩ := Classical.axiomOfChoice f.surj
  refine ⟨{
    toFun := f
    invFun := g
    leftInv := hg
    rightInv b := by apply f.inj; rw [hg]
  }⟩
