import LeanMath.Data.Countable.Defs
import LeanMath.Logic.Small.Defs

instance [h: IsCountable α] : Small.{0} α := by
  obtain ⟨h⟩ := h
  exact .intro (Encoding α) (Equiv.encoding _)
