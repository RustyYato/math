import LeanMath.Algebra.Module.Defs
import LeanMath.Algebra.Group.Action.Defs
import LeanMath.Algebra.Ring.Defs

variable [RingOps R] [IsRing R] [AddGroupOps α] [IsAddGroup α]
  [IsAddComm α] [SMul R α] [IsModule R α]

instance : IsScalarTower ℤ R α where
  smul_assoc n r a := by
    cases n with
    | ofNat => simp [ofNat_zsmul, smul_assoc]
    | negSucc => simp [negSucc_zsmul, ←neg_smul_left, smul_assoc]
