import LeanMath.Algebra.Monoid.Defs

class AddMonoidWithOneOps (α: Type*) extends AddMonoidOps α, One α, NatCast α where

instance (priority := 1100) [AddMonoidOps α] [One α] [NatCast α] : AddMonoidWithOneOps α where

class IsLawfulNatCast (α: Type*) [Add α] [Zero α] [One α] [NatCast α] where
  protected natCast_zero : (0: ℕ) = (0: α)
  protected natCast_one : (1: ℕ) = (1: α)
  protected natCast_succ (n: ℕ) : (n + 1: ℕ) = (n: α) + 1

class IsAddMonoidWithOne (α: Type*) [AddMonoidWithOneOps α] : Prop extends IsAddMonoid α, IsLawfulNatCast α where

section

variable [Add α] [Zero α] [One α] [NatCast α] [IsLawfulNatCast α]
  [Add β] [Zero β] [One β] [NatCast β] [IsLawfulNatCast β]
  [FunLike F α β] [IsAddHom F α β] [IsZeroHom F α β] [IsOneHom F α β]

def natCast_zero : (0: ℕ) = (0: α) := IsLawfulNatCast.natCast_zero
def natCast_one : (1: ℕ) = (1: α) := IsLawfulNatCast.natCast_one
def natCast_succ (n: ℕ) : (n + 1: ℕ) = (n: α) + 1 := IsLawfulNatCast.natCast_succ _

def natCast_add [IsLawfulZeroAdd α] [IsAddSemigroup α] (n m: ℕ) : (n + m: ℕ) = (n: α) + m := by
  induction m with
  | zero => rw [natCast_zero, add_zero, add_zero]
  | succ m ih => rw [Nat.add_succ, natCast_succ, natCast_succ, ih, add_assoc]

def map_natCast (f: F) (n: ℕ) : f n = n := by
  induction n with
  | zero => rw [natCast_zero, natCast_zero, map_zero]
  | succ n ih => rw [natCast_succ, natCast_succ, map_add, map_one, ih]

def natCastHom₀ [IsLawfulZeroAdd α] [IsAddSemigroup α] : ℕ →+ α where
  toFun n := n
  map_zero := natCast_zero
  map_add := natCast_add

end

section

variable
  [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] [AddMonoidWithOneOps β] [IsAddMonoidWithOne β]

def natCast_eq_nsmul_one (n: ℕ) : (n: α) = n • 1 := by
  induction n with
  | zero => rw [natCast_zero, zero_nsmul]
  | succ n ih =>  rw [natCast_succ, ih, succ_nsmul]

end

instance : IsLawfulNatCast ℕ where
  natCast_zero := rfl
  natCast_one := rfl
  natCast_succ _ := rfl

instance : IsAddMonoidWithOne ℕ where

instance : IsLawfulNatCast ℤ where
  natCast_zero := rfl
  natCast_one := rfl
  natCast_succ _ := rfl

instance : IsAddMonoidWithOne ℤ where
