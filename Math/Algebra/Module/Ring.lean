module

public import Math.Algebra.Module.Defs
public import Math.Algebra.Ring.Defs
public import Math.Algebra.Group.Action.Defs

namespace Math

instance [AddGroupOps α] [IsAddGroup α] [IsAddComm α] : IsModule ℤ α where
