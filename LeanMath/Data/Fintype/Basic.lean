import LeanMath.Data.Fintype.Pi
import LeanMath.Data.Fintype.Sigma
import LeanMath.Data.Fintype.Pairing

noncomputable scoped instance (priority := 10) Classical.instFintypeOfFinite [f: Finite α] : Fintype α :=
  Classical.choice f

namespace Finite

private def ofEmbed' [LEM] (emb: α ↪ Fin n) : Finite α := by
  induction n with
  | zero =>
    · have : IsEmpty α := {
        elim a := elim_empty (emb a)
      }
      infer_instance
  | succ n ih =>
    rcases em (Function.Surjective emb) with hf | hf
    · have bij : α ↭ Fin (n + 1) := {
        toFun := emb
        inj' := emb.inj
        surj' := hf
      }
      apply ofBij (α := Fin _)
      exact (Equiv.ofBij bij).symm.toBij
    · obtain ⟨x, hx⟩ := LEM.not_forall.mp hf
      rw [not_exists] at hx
      exact ih (emb.erase_fin _ hx)

def ofEmbed [LEM] [hf: Finite β] (emb: α ↪ β) : Finite α := by
  obtain ⟨hf⟩ := hf
  open UniqueChoice in
  induction Fintype.finEquiv β with | _ f =>
  apply ofEmbed'
  exact emb.trans f.symm.toEmbedding

end Finite
