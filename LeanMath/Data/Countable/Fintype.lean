import LeanMath.Data.Fintype.Defs
import LeanMath.Data.Countable.Defs

instance [DecidableEq α] [h: Finite α] : IsCountable α := by
  obtain ⟨h⟩ := h
  induction h.finEquiv with | _ h =>
  apply Nonempty.intro
  apply Encodable.ofEquiv h
