module

public import Math.Algebra.Monoid.Action.Defs.Basic
public import Math.Algebra.Monoid.Defs.Hom

namespace Math

@[expose] public def smulHom {α β: Type*}
  [Zero α] [Add α]
  [Zero β] [Add β]
  [SMul α β]
  [IsLawfulZeroSMul α β]
  [IsLeftDistribSMul α β]
  (b: β) : α →+ β where
  toFun a := a • b
  map_zero := by rw [zero_smul]
  map_add _ _ := by rw [add_smul]
