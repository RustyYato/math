module

public import Math.Algebra.RingQuot.Defs
public import Math.Algebra.Ring.Congruence

namespace Math.RingQuot

variable {r: α -> α -> Prop}

def ofQuot' [SemiringOps α] (r: α -> α -> Prop) : AlgQuot (RingCon.generate r) ≃ RingQuot r where
  toFun := RingQuot.ofQuot
  invFun := RingQuot.toQuot
  leftInv _ := rfl
  rightInv _ := rfl

instance [RingOps α] [IsRing α] : RingOps (RingQuot r) where
  sub a b := ⟨a.toQuot - b.toQuot⟩
  neg a := ⟨-a.toQuot⟩
  intCast n := ⟨n⟩
  toZSMul := ⟨fun n a => ⟨n • a.toQuot⟩⟩

instance [RingOps α] [IsRing α] : IsRing (RingQuot r) :=
  OfEquiv.instIsRing (RingQuot.ofQuot' r)
