import LeanMath.Order.Defs
import LeanMath.Data.Set.Defs

namespace Set

variable [LE α] [LT α]

def upperBounds (s: Set α) : Set α where
  Mem x := ∀a ∈ s, a ≤ x

def lowerBounds (s: Set α) : Set α where
  Mem x := ∀a ∈ s, x ≤ a

def isMaximal (s: Set α) (x: α) : Prop := ∀a ∈ s, x ≤ a -> a ≤ x
def isMax (s: Set α) (x: α) : Prop := ∀a ∈ s, a ≤ x
def isMinimal (s: Set α) (x: α) : Prop := ∀a ∈ s, a ≤ x -> x ≤ a
def isMin (s: Set α) (x: α) : Prop := ∀a ∈ s, x ≤ a

def IsGLB (s: Set α) (x: α) := s.lowerBounds.isMax x
def IsLUB (s: Set α) (x: α) := s.upperBounds.isMin x

def BoundedAbove (s: Set α) := s.upperBounds.Nonempty
def BoundedBelow (s: Set α) := s.lowerBounds.Nonempty

end Set
