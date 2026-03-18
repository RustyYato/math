import LeanMath.Data.Fintype.Pi
import LeanMath.Data.Fintype.Sigma
import LeanMath.Data.Fintype.Pairing

noncomputable scoped instance (priority := 10) Classical.instFintypeOfFinite [f: Finite α] : Fintype α :=
  Classical.choice f

namespace Finite

private def ofEmbed' (emb: α ↪ Fin n) : Finite α := by
  open Classical in
  induction n with
  | zero =>
    · have : IsEmpty α := {
        elim a := elim_empty (emb a)
      }
      infer_instance
  | succ n ih =>
    by_cases hf:Function.Surjective emb
    · have bij : α ↭ Fin (n + 1) := {
        toFun := emb
        inj' := emb.inj
        surj' := hf
      }
      apply ofBij (α := Fin _)
      exact bij.symm
    · simp [Function.Surjective] at hf
      obtain ⟨x, hx⟩ := hf
      exact ih (emb.erase_fin _ hx)

def ofEmbed [Finite β] (emb: α ↪ β) : Finite α := by
  open Classical in
  induction Fintype.finEquiv β with | _ f =>
  apply ofEmbed'
  exact emb.trans f.symm.toEmbedding

end Finite
