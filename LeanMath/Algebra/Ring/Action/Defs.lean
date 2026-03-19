import LeanMath.Algebra.Semiring.Action.Defs
import LeanMath.Algebra.Group.Action.Defs
import LeanMath.Algebra.Ring.Defs

variable [AddGroupOps α] [IsAddGroup α]

instance [IsAddComm α] : IsModule ℤ α where

variable [RingOps R] [IsRing R] [SMul R α]
