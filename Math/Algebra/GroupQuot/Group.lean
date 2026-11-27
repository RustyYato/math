module

public import Math.Algebra.GroupQuot.Defs
public import Math.Algebra.Group.Congruence
public import Math.Algebra.Group.Defs.OfEquiv

namespace Math.GroupQuot

variable {r: α -> α -> Prop}

def ofQuot' [MonoidOps α] (r: α -> α -> Prop) : AlgQuot (MulCon.generate r) ≃ GroupQuot r where
  toFun := GroupQuot.ofQuot
  invFun := GroupQuot.toQuot
  leftInv _ := rfl
  rightInv _ := rfl

public instance [GroupOps α] [IsGroup α] : GroupOps (GroupQuot r) where
  div a b := ⟨a.toQuot / b.toQuot⟩
  inv a := ⟨a.toQuot⁻¹⟩
  toPowZ := ⟨fun a n => ⟨a.toQuot ^ n⟩⟩

public instance [GroupOps α] [IsGroup α] : IsGroup (GroupQuot r) :=
  OfEquiv.instIsGroup (ofQuot' r)
