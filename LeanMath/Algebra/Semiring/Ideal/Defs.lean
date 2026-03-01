import LeanMath.Algebra.Semiring.Set

class IsMemLeftMul (S α: Type*) [SetLike S α] [SemiringOps α] [IsSemiring α] where
  protected mem_left_mul (s: S) {a: α} (k: α) : a ∈ s -> k * a ∈ s := by intro s; exact s.mem_left_mul

class IsMemRightMul (S α: Type*) [SetLike S α] [SemiringOps α] [IsSemiring α] where
  protected mem_right_mul (s: S) {a: α} (k: α) : a ∈ s -> a * k ∈ s := by intro s; exact s.mem_right_mul

variable [SetLike S α] [SemiringOps α] [IsSemiring α]

def mem_left_mul [IsMemLeftMul S α] (s: S) {a: α} (k: α) : a ∈ s -> k * a ∈ s :=
  IsMemLeftMul.mem_left_mul _ _

def mem_right_mul [IsMemRightMul S α] (s: S) {a: α} (k: α) : a ∈ s -> a * k ∈ s :=
  IsMemRightMul.mem_right_mul _ _

structure SubLeftMul (α: Type*) [SemiringOps α] [IsSemiring α] where
  toSet: Set α
  protected mem_left_mul {a: α} (k: α) : a ∈ toSet -> k * a ∈ toSet

structure SubRightMul (α: Type*) [SemiringOps α] [IsSemiring α] where
  toSet: Set α
  protected mem_right_mul {a: α} (k: α) : a ∈ toSet -> a * k ∈ toSet

instance : SetLike (SubLeftMul α) α where
instance : IsMemLeftMul (SubLeftMul α) α where

instance : SetLike (SubRightMul α) α where
instance : IsMemRightMul (SubRightMul α) α where
