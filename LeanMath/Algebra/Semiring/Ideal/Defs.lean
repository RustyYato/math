import LeanMath.Algebra.Semiring.Defs
import LeanMath.Data.Set.Defs

def MemLeftMul [SetLike S α] [Mul α] (s: S) := ∀{a: α} (k: α), a ∈ s -> k * a ∈ s
def MemRightMul [SetLike S α] [Mul α] (s: S) := ∀{a: α} (k: α), a ∈ s -> a * k ∈ s

class IsMemLeftMul (S α: Type*) [SetLike S α] [Mul α] where
  protected mem_left_mul (s: S) : MemLeftMul s := by intro s; exact s.mem_left_mul

class IsMemRightMul (S α: Type*) [SetLike S α] [Mul α] where
  protected mem_right_mul (s: S) : MemRightMul s := by intro s; exact s.mem_right_mul

variable [Mul α] [Mul β]

section

variable [SetLike S α]

def mem_left_mul [IsMemLeftMul S α] (s: S) : MemLeftMul s:=
  IsMemLeftMul.mem_left_mul _

def mem_right_mul [IsMemRightMul S α] (s: S) : MemRightMul s :=
  IsMemRightMul.mem_right_mul _

end

structure SubLeftMul (α: Type*) [Mul α] where
  toSet: Set α
  protected mem_left_mul : MemLeftMul toSet

structure SubRightMul (α: Type*) [Mul α] where
  toSet: Set α
  protected mem_right_mul : MemRightMul toSet

instance : SetLike (SubLeftMul α) α where
instance : IsMemLeftMul (SubLeftMul α) α where

instance : SetLike (SubRightMul α) α where
instance : IsMemRightMul (SubRightMul α) α where

def MemLeftMul.preimage [SetLike S β] [IsMemLeftMul S β] [FunLike F α β] [IsMulHom F α β] (f: F) (s: S) : MemLeftMul (Set.preimage f s) := by
  intro a k ha
  simp; rw [map_mul]
  apply mem_left_mul s
  assumption

def MemRightMul.preimage [SetLike S β] [IsMemRightMul S β] [FunLike F α β] [IsMulHom F α β] (f: F) (s: S) : MemRightMul (Set.preimage f s) := by
  intro a k ha
  simp; rw [map_mul]
  apply mem_right_mul s
  assumption
