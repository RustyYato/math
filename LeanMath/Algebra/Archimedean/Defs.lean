import LeanMath.Algebra.Monoid.Order

class IsArchimedean (α: Type*) [LE α] [LT α] [AddMonoidOps α] [IsOrderedAddCommMonoid α] where
  archidedean: ∀(x: α) {y: α}, 0 < y -> ∃n: ℕ, x ≤ n • y

def archidedean [LE α] [LT α] [AddMonoidOps α] [IsOrderedAddCommMonoid α] [IsArchimedean α]: ∀(x: α) {y: α}, 0 < y -> ∃n: ℕ, x ≤ n • y :=
  IsArchimedean.archidedean


instance : IsArchimedean ℕ where
  archidedean x {y} hy := by
    exists x
    rw [smul_eq_mul]
    apply le_mul_right
    apply Nat.succ_le_of_lt
    assumption

instance : IsArchimedean ℤ where
  archidedean x {y} hy := by
    exists x.natAbs
    apply le_trans
    exact Int.le_natAbs
    rw [←mul_one (Nat.cast x.natAbs)]
    apply Int.mul_le_mul_of_nonneg_left
    · exact Int.le_of_sub_one_lt hy
    · exact Int.natCast_nonneg x.natAbs
