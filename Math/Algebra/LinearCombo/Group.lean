module

public import Math.Algebra.LinearCombo.Defs
public import Math.Algebra.DirectSum.Ring

namespace Math.LinearCombo

section

variable {ι α: Type*} [AddGroupOps α] [IsAddGroup α] [IsAddComm α]

public instance : Neg (LinearCombo ι α) where
  neg a := ⟨-a.toDirectSum⟩
public instance : Sub (LinearCombo ι α) where
  sub a b := ⟨a.toDirectSum - b.toDirectSum⟩
public instance : SMul ℤ (LinearCombo ι α) where
  smul n a := ⟨n • a.toDirectSum⟩

public instance : IsAddGroup (LinearCombo ι α) :=
  OfEquiv.instIsAddGroup addEqv.toEquiv

end

variable {ι α: Type*} [RingOps α] [IsRing α]

public theorem get_inj [DecidableEq ι] : Function.Injective fun lc: LinearCombo ι α => (LinearCombo.get · lc) := by
  intro a b h;
  dsimp at h
  replace h (i: ι) := congrFun h i
  sorry
