import LeanMath.Algebra.Monoid.Defs

variable {α: Type*} {M: α -> Type*}

class GradedOne {α: Type*} (M: α -> Type*) [Zero α] where
  gOne: M 0

class GradedMul {α: Type*} (M: α -> Type*) [Add α] where
  gMul {a b: α}: M a -> M b -> M (a + b)

class GradedPow {α: Type*} (M: α -> Type*) (β: Type*) [SMul β α] where
  gPow {a: α}: M a -> ∀b: β, M (b • a)

structure Graded {α: Type*} (M: α -> Type*) where
  level: α
  val: M level

instance [Zero α] [GradedOne M] : One (Graded M) where
  one := ⟨0, GradedOne.gOne⟩
instance [Add α] [GradedMul M] : Mul (Graded M) where
  mul a b := ⟨a.level + b.level, GradedMul.gMul a.val b.val⟩
instance [SMul β α] [GradedPow M β] : Pow (Graded M) β where
  pow a b := ⟨b • a.level, GradedPow.gPow a.val b⟩

abbrev IsLawfulGradedSemigroup (M: α -> Type*)
  [Add α] [IsAddSemigroup α] [GradedMul M] :=
  IsSemigroup (Graded M)
abbrev IsLawfulGradedComm (M: α -> Type*)
  [Add α] [IsAddSemigroup α] [GradedMul M] :=
  IsComm (Graded M)
abbrev IsLawfulGradedOneMul (M: α -> Type*)
  [AddMonoidOps α] [IsAddMonoid α] [GradedOne M] [GradedMul M] :=
  IsLawfulOneMul (Graded M)
abbrev IsLawfulGradedPowN (M: α -> Type*)
  [AddMonoidOps α] [IsAddMonoid α] [GradedOne M] [GradedMul M] [GradedPow M ℕ] :=
  IsLawfulPowN (Graded M)
abbrev IsGradedMonoid (M: α -> Type*)
  [AddMonoidOps α] [IsAddMonoid α] [GradedOne M] [GradedMul M] [GradedPow M ℕ] :=
  IsMonoid (Graded M)
