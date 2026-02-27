import LeanMath.Algebra.Group.Defs
import LeanMath.Algebra.AddMonoidWithOne.Defs

class AddGroupWithOneOps (α: Type*) extends AddMonoidWithOneOps α, AddGroupOps α, IntCast α where

instance (priority := 1100)
  [AddMonoidWithOneOps α] [AddGroupOps α] [IntCast α]
  : AddGroupWithOneOps α where

class IsLawfulIntCast (α: Type*) [NatCast α] [IntCast α] [Neg α] where
  protected intCast_ofNat (n: ℕ) : (n: ℤ) = (n: α)
  protected intCast_negSucc (n: ℕ) : (Int.negSucc n) = -((n + 1: ℕ): α)

class IsAddGroupWithOne (α: Type*) [AddGroupWithOneOps α] : Prop extends IsAddMonoidWithOne α, IsAddGroup α, IsLawfulIntCast α where

section

variable [NatCast α] [IntCast α] [Neg α] [IsLawfulIntCast α]

def intCast_ofNat (n: ℕ) : (n: ℤ) = (n: α) := IsLawfulIntCast.intCast_ofNat _
def intCast_negSucc (n: ℕ) : (Int.negSucc n) = -((n + 1: ℕ): α) := IsLawfulIntCast.intCast_negSucc _

end

instance : IsLawfulIntCast ℤ where
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

section

variable [AddGroupWithOneOps α] [IsAddGroupWithOne α]
   [AddGroupWithOneOps β] [IsAddGroupWithOne β]
   [FunLike F α β] [IsAddHom F α β] [IsZeroHom F α β] [IsOneHom F α β]

def intCast_zero : (0: ℤ) = (0: α) := by
  show ((0: ℕ): ℤ) = (0: α)
  rw [intCast_ofNat, natCast_zero]
def intCast_one : (1: ℤ) = (1: α) := by
  show ((1: ℕ): ℤ) = (1: α)
  rw [intCast_ofNat, natCast_one]

def intCast_eq_zsmul_one (n: ℤ) : (n: α) = n • 1 := by
  cases n with
  | ofNat n => rw [intCast_ofNat, natCast_eq_nsmul_one, ofNat_zsmul]
  | negSucc n => rw [intCast_negSucc, natCast_eq_nsmul_one, negSucc_zsmul]

def intCast_neg (n: ℤ) : (-n: ℤ) = -(n: α) := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, neg_zsmul]

def intCast_add (n m: ℤ) : (n + m: ℤ) = (n: α) + m := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, intCast_eq_zsmul_one, add_zsmul]

def intCast_sub (n m: ℤ) : (n - m: ℤ) = (n: α) - m := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, intCast_eq_zsmul_one, sub_zsmul]

def zsmul_intCast (n m: ℤ) : n • (m: α) = (n * m: ℤ) := by
  rw [intCast_eq_zsmul_one, intCast_eq_zsmul_one, mul_comm, mul_zsmul]

def map_intCast (f: F) (n: ℤ) : f n = n := by
  cases n with
  | ofNat n => rw [intCast_ofNat, intCast_ofNat, map_natCast]
  | negSucc n => rw [intCast_negSucc,intCast_negSucc, map_neg, map_natCast]

def intCastHom₀ : ℤ →+₁ α where
  toFun n := n
  map_zero := intCast_zero
  map_one := intCast_one
  map_add := intCast_add

end

instance : IsAddGroupWithOne ℤ where
