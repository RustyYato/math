import LeanMath.Algebra.Monoid.Defs

noncomputable def defaultNatCastFun (α: Type*) [AddMonoidOps α] [IsAddMonoid α] [One α] : Nat -> α
| 0 => 0
| n + 1 => defaultNatCastFun α n + 1

private def fast_defaultNatCastFun (α: Type*) [AddMonoidOps α] [IsAddMonoid α] [One α] (n: ℕ) : α :=
  if n = 0 then 0 else
  let na := fast_defaultNatCastFun α (n / 2)
  if n % 2 = 0 then na + na else na + na + 1

private def defaultNatCastFun_eq_smul_one [AddMonoidOps α] [IsAddMonoid α] [One α] (n: ℕ) : defaultNatCastFun α n = n • 1 := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    rfl
  | succ n ih =>
    rw [succ_nsmul, ←ih]
    rfl

private def fast_defaultNatCastFun_eq_smul_one [AddMonoidOps α] [IsAddMonoid α] [One α] (n: ℕ) : fast_defaultNatCastFun α n = n • 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  match n with
  | 0 => simp [fast_defaultNatCastFun, zero_nsmul]
  | 1 => simp [fast_defaultNatCastFun, zero_add, one_nsmul]
  | n + 2 =>
    unfold fast_defaultNatCastFun
    rw [if_neg nofun]
    rw [ih _ (by omega)]
    simp
    split <;> rename_i h
    · rw [←add_nsmul, ←Nat.two_mul, Nat.mul_add, mul_one,
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)]
    · rw (occs := [3]) [←one_nsmul (1: α)]
      rw [←add_nsmul, ←add_nsmul, ←Nat.two_mul]
      rw (occs := [2]) [show 1 = (n + 2) % 2 by omega]
      rw [←Nat.add_mul_div_left, mul_one]
      rw [Nat.div_add_mod]
      omega

@[csimp]
private def defaultNatCastFun_eq_fast : defaultNatCastFun = fast_defaultNatCastFun := by
  ext α _ _ _ n
  rw [defaultNatCastFun_eq_smul_one]
  rw [fast_defaultNatCastFun_eq_smul_one]

def defaultNatCast (α: Type*) [AddMonoidOps α] [IsAddMonoid α] [One α] : NatCast α := ⟨defaultNatCastFun α⟩

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

structure AddGroupWithOneHom (α β: Type*) [Zero α] [Zero β] [One α] [One β] [Add α] [Add β] extends Hom α β, α →₀ β, α →₁ β, α →+ₙ β, α →+ β where

infixr:80 " →+₁ " => AddGroupWithOneHom

instance : FunLike (α →+₁ β) α β where
instance : IsZeroHom (α →+₁ β) α β where
instance : IsOneHom (α →+₁ β) α β where
instance : IsAddHom (α →+₁ β) α β where

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

def natCastHom₀ [IsLawfulZeroAdd α] [IsAddSemigroup α] : ℕ →+₁ α where
  toFun n := n
  map_zero := natCast_zero
  map_one := natCast_one
  map_add := natCast_add

end

section

variable
  [AddMonoidWithOneOps α] [IsAddMonoidWithOne α] [AddMonoidWithOneOps β] [IsAddMonoidWithOne β]

def natCast_eq_nsmul_one (n: ℕ) : (n: α) = n • 1 := by
  induction n with
  | zero => rw [natCast_zero, zero_nsmul]
  | succ n ih =>  rw [natCast_succ, ih, succ_nsmul]

variable [RelLike R α] [IsCon R] [IsAddCon R] (r: R)

instance : IsAddMonoidWithOne (AlgQuot r) where
  natCast_zero := by
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [natCast_zero]
  natCast_one := by
    show AlgQuot.mk r _ = AlgQuot.mk r _
    rw [natCast_one]
  natCast_succ n := by
    show AlgQuot.mk r _ = AlgQuot.mk r _ + AlgQuot.mk r _
    rw [natCast_succ, map_add]

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
