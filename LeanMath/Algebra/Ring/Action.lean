import LeanMath.Algebra.Semiring.Action
import LeanMath.Algebra.Group.Action
import LeanMath.Algebra.Ring.Defs

instance [AddGroupOps α] [IsAddGroup α] [IsAddComm α] : IsModule ℤ α where
