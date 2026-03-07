import LeanMath.Algebra.Module.Defs
import LeanMath.Algebra.Ring.Defs

variable [RingOps R] [IsRing R] [AddGroupOps α] [IsAddGroup α]
  [IsAddComm α] [SMul R α] [IsModule R α]

def neg_smul (r: R) (a: α) : (-r) • a = -(r • a) := by
  apply eq_neg_of_add
  rw [←add_smul, neg_add_cancel, zero_smul]

instance : IsScalarTower ℤ R α where
  smul_assoc n r a := by
    cases n with
    | ofNat => simp [ofNat_zsmul, smul_assoc]
    | negSucc => simp [negSucc_zsmul, neg_smul, smul_assoc]
