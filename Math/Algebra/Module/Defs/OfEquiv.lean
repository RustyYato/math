module

public import Math.Algebra.Module.Defs.Basic
public import Math.Algebra.Monoid.Action.Defs.OfEquiv

namespace Math.OfEquiv

variable (f: α ≃ β)
  [SemiringOps R] [IsSemiring R]
  [AddMonoidOps α] [IsAddMonoid α]
  [SMul R α] [IsModule R α]

public instance : IsModule R (OfEquiv f) where
