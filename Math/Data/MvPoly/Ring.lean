module

public import Math.Data.MvPoly.Defs
public import Math.Algebra.DirectSum.Ring
public import Math.Algebra.Ring.Defs.OfEquiv

namespace Math

namespace MvPoly

variable {ι α: Type*} [RingOps α] [IsRing α]

public instance : RingOps (MvPoly ι α) where
  neg a := ⟨-a.toDirectSum⟩
  sub a b := ⟨a.toDirectSum - b.toDirectSum⟩
  toZSMul := ⟨fun n a => ⟨n • a.toDirectSum⟩⟩
  intCast n := ⟨n⟩

public instance : IsRing (MvPoly ι α) :=
  OfEquiv.instIsRing eqv.toEquiv
