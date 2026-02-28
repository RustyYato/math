import LeanMath.Algebra.Group.Defs
import LeanMath.Algebra.Monoid.Set

class IsMemInv (S α: Type*) [Inv α] [SetLike S α] where
  protected mem_inv (s: S) {a: α}: a ∈ s -> a⁻¹ ∈ s := by intro s; exact s.mem_inv

class IsMemNeg (S α: Type*) [Neg α] [SetLike S α] where
  protected mem_neg (s: S) {a: α}: a ∈ s -> -a ∈ s := by intro s; exact s.mem_neg

def mem_inv [Inv α] [SetLike S α] [IsMemInv S α] (s: S) {a: α}: a ∈ s -> a⁻¹ ∈ s :=
  IsMemInv.mem_inv _

def mem_neg [Neg α] [SetLike S α] [IsMemNeg S α] (s: S) {a: α}: a ∈ s -> -a ∈ s :=
  IsMemNeg.mem_neg _

structure SubInv (α: Type*) [Inv α] where
  toSet: Set α
  protected mem_inv {a: α} : a ∈ toSet -> a⁻¹ ∈ toSet

structure SubNeg (α: Type*) [Neg α] where
  toSet: Set α
  protected mem_neg {a: α} : a ∈ toSet -> -a ∈ toSet

instance [Inv α] : SetLike (SubInv α) α where
instance [Inv α] : IsMemInv (SubInv α) α where

instance [Neg α] : SetLike (SubNeg α) α where
instance [Neg α] : IsMemNeg (SubNeg α) α where

structure Subgroup (α: Type*) [Mul α] [Inv α] [One α] extends SubMonoid α, SubInv α where

structure AddSubgroup (α: Type*) [Add α] [Neg α] [Zero α] extends AddSubMonoid α, SubNeg α where

instance [Mul α] [Inv α] [One α] : SetLike (Subgroup α) α where
instance [Mul α] [Inv α] [One α] : IsMemMul (Subgroup α) α where
instance [Mul α] [Inv α] [One α] : IsMemInv (Subgroup α) α where
instance [Mul α] [Inv α] [One α] : IsMemOne (Subgroup α) α where

instance [Add α] [Neg α] [Zero α] : SetLike (AddSubgroup α) α where
instance [Add α] [Neg α] [Zero α] : IsMemAdd (AddSubgroup α) α where
instance [Add α] [Neg α] [Zero α] : IsMemNeg (AddSubgroup α) α where
instance [Add α] [Neg α] [Zero α] : IsMemZero (AddSubgroup α) α where

variable (s: S) [SetLike S α]

section

instance [Inv α] [IsMemInv S α] : Inv s where
  inv a := {
    val := a.val⁻¹
    property := mem_inv s a.property
  }

instance [Neg α] [IsMemNeg S α] : Neg s where
  neg a := {
    val := -a.val
    property := mem_neg s a.property
  }

instance [Neg α] [IsMemNeg S α] : IsMemInv (MulOfAdd S) (MulOfAdd α) where
  mem_inv a := mem_neg a.get

instance [Inv α] [IsMemInv S α] : IsMemNeg (AddOfMul S) (AddOfMul α) where
  mem_neg a := mem_inv a.get

end

section

variable [GroupOps α] [IsGroup α] [IsMemMul S α] [IsMemInv S α] [IsMemOne S α]

def mem_zpow {a: α} (n: ℤ) : a ∈ s -> a ^ n ∈ s := by
  intro h
  cases n with
  | ofNat n =>
    rw [zpow_ofNat]
    apply mem_npow
    assumption
  | negSucc =>
    rw [zpow_negSucc]
    apply mem_inv
    apply mem_npow
    assumption

def mem_div {a b: α} : a ∈ s -> b ∈ s -> a / b ∈ s := by
  intro h g
  rw [div_eq_mul_inv]
  apply mem_mul
  assumption
  apply mem_inv
  assumption

instance : Pow s ℤ where
  pow a n := {
    val := a.val ^ n
    property := mem_zpow s n a.property
  }

instance : Div s where
  div a b := {
    val := a.val / b.val
    property := mem_div s a.property b.property
  }

instance : IsGroup s where
  div_eq_mul_inv _ _ := by
    apply Subtype.val_inj
    apply div_eq_mul_inv
  zpow_ofNat _ _ := by
    apply Subtype.val_inj
    apply zpow_ofNat
  zpow_negSucc _ _ := by
    apply Subtype.val_inj
    apply zpow_negSucc
  mul_inv_cancel _ := by
    apply Subtype.val_inj
    apply mul_inv_cancel

end

section

variable [AddGroupOps α] [IsAddGroup α] [IsMemAdd S α] [IsMemNeg S α] [IsMemZero S α]

def mem_zsmul {a: α} (n: ℤ) : a ∈ s -> n • a ∈ s :=
  mem_zpow (MulOfAdd.mk s) n

def mem_sub {a b: α} : a ∈ s -> b ∈ s -> a - b ∈ s :=
  mem_div (MulOfAdd.mk s)

instance : SMul ℤ s where
  smul n a := {
    val := n • a.val
    property := mem_zsmul s n a.property
  }

instance : Sub s where
  sub a b := {
    val := a.val - b.val
    property := mem_sub s a.property b.property
  }

instance : IsAddGroup s where
  sub_eq_add_neg _ _ := by
    apply Subtype.val_inj
    apply sub_eq_add_neg
  ofNat_zsmul _ _ := by
    apply Subtype.val_inj
    apply ofNat_zsmul
  negSucc_zsmul _ _ := by
    apply Subtype.val_inj
    apply negSucc_zsmul
  add_neg_cancel _ := by
    apply Subtype.val_inj
    apply add_neg_cancel

end
