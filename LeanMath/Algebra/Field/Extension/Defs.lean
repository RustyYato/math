import LeanMath.Algebra.Field.Defs
import LeanMath.Data.Poly.Defs
import LeanMath.Data.Set.Defs

-- an extension of `α` is a larger field `β` which contains `α`
class IsExtension (α β: Type*) [FieldOps α] [FieldOps β] [IsField α] [IsField β] where
  exists_extension: Nonempty (α →+* β)

-- an strict extension of `α` is a strictly larger field `β` which contains `α`
class IsStrictExtension (α β: Type*) [FieldOps α] [FieldOps β] [IsField α] [IsField β] extends IsExtension α β where
  is_strict_extension: IsEmpty (β →+* α)

class IsAlgebraicExtension (α β: Type*)
  [SemiringOps α] [SemiringOps β] [IsSemiring α] [IsComm α] [IsSemiring β] [IsComm β]
  [AlgebraMap α β] [SMul α β] [IsAlgebra α β] where
  -- an algebraic extension `β` of `α` is one where every value of `β`
  -- is a root of a `α`-polynomial
  exists_root_of_poly (b: β) : ∃p: α[X], Poly.eval α b p = 0

instance [FieldOps α] [FieldOps β] [IsField α] [IsField β] [AlgebraMap α β] : IsExtension α β where
  exists_extension := ⟨algebraMap α⟩
