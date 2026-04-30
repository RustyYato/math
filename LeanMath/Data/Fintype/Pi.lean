import LeanMath.Data.FinEncodable.Pi

namespace Fintype

section

variable {ι: Sort*} {α: ι -> Sort*} [fι: Fintype ι] [DecidableEq ι] [fα: ∀i, Fintype (α i)]

instance (priority := 100) : Fintype (∀i, α i) :=
  (truncFinEncodable (inferInstance: Fintype ι)).recOnSubsingleton fun _ =>
  (finTruncChoice (fun i => (truncFinEncodable (inferInstance: Fintype (α i))))).recOnSubsingleton fun _ =>
  inferInstance

end

section

variable {ι α: Sort*} [fι: Fintype ι] [DecidableEq ι] [fα: Fintype α]

instance (priority := 10000) instFunc : Fintype (ι -> α) :=
  (truncFinEncodable (inferInstance: Fintype ι)).recOnSubsingleton fun _ =>
  (truncFinEncodable (inferInstance: Fintype α)).recOnSubsingleton fun _ =>
  Fintype.instOfFinEncodable

end

end Fintype

namespace Finite

variable
  {α: ι -> Sort*}
  [fι: Finite ι] [DecidableEq ι] [fα: ∀i, Finite (α i)]

instance : Finite (∀i, α i) := by
  have ⟨fα⟩ := finChoose fα
  obtain ⟨fι⟩ := fι
  have : DecidableEq ι := inferInstance
  exact ⟨inferInstance⟩

end Finite

namespace Finite

variable
  {α: Sort*}
  [fι: Finite ι] [DecidableEq ι] [fα: Finite α]

instance : Finite (ι -> α) := inferInstance

end Finite
