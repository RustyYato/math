module

public import Math.Algebra.LinearQuot.Defs
public import Math.Algebra.Group.Congruence

namespace Math.LinearQuot

variable (R: Type*) {r: α -> α -> Prop}

instance [AddGroupOps α] [IsAddGroup α] [SMul R α] : AddGroupOps (LinearQuot R r) where
  neg a := ⟨-a.toQuot⟩
  sub a b := ⟨a.toQuot - b.toQuot⟩
  toZSMul := ⟨fun n a => ⟨n • a.toQuot⟩⟩

instance [AddGroupOps α] [IsAddGroup α] [SMul R α] : IsAddGroup (LinearQuot R r) where
  sub_eq_add_neg a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    show LinearQuot.mk R r _ = LinearQuot.mk R r _
    rw [sub_eq_add_neg]
  neg_add_cancel a := by
    induction a with | _ a =>
    show LinearQuot.mk R r _ = LinearQuot.mk R r _
    rw [neg_add_cancel]
  ofNat_zsmul a b := by
    induction a with | _ a =>
    show LinearQuot.mk R r _ = LinearQuot.mk R r _
    rw [ofNat_zsmul]
  negSucc_zsmul a b := by
    induction a with | _ a =>
    show LinearQuot.mk R r _ = LinearQuot.mk R r _
    rw [negSucc_zsmul]
