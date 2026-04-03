import LeanMath.Algebra.Algebra.Defs
import LeanMath.Algebra.Monoid.Action.Set
import LeanMath.Algebra.Semiring.Set

def MemAlgebraMap [SetLike S α] (R: Type*)
  [SemiringOps R] [SemiringOps α]
  [AlgebraMap R α] (s: S) :=
  ∀(r: R), algebraMap R r ∈ s

class IsMemAlgebraMap (S R α: Type*) [SetLike S α] [SemiringOps R] [SemiringOps α] [AlgebraMap R α] where
  protected mem_algebraMap (s: S) : MemAlgebraMap R s := by intro s; exact s.mem_algebraMap

structure SubAlgebraMap (R α: Type*) [SemiringOps R] [SemiringOps α] [AlgebraMap R α] where
  toSet : Set α
  protected mem_algebraMap : MemAlgebraMap R toSet

-- this represents a unital sub-algebra of `α`, since `r • 1 = algebraMap R r`
-- and `a ∈ s -> r • a ∈ s`, we can simplify conditions and only require
-- that `algebraMap R r ∈ s` and `a ∈ s -> b ∈ s -> a * b ∈ s`
-- to get the full scope when we know that `[IsAlgebra R α]`
structure NonUnitalSubalgebra (R α: Type*) [Zero α] [Add α] [Mul α] [SMul R α] extends SubSemigroup α, Submodule R α where

-- this represents a unital sub-algebra of `α`, since `r • 1 = algebraMap R r`
-- and `a ∈ s -> r • a ∈ s`, we can simplify conditions and only require
-- that `algebraMap R r ∈ s` and `a ∈ s -> b ∈ s -> a * b ∈ s`
-- to get the full scope when we know that `[IsAlgebra R α]`
structure Subalgebra (R α: Type*) [SemiringOps R] [SemiringOps α] [AlgebraMap R α]
  extends AddSubSemigroup α, SubSemigroup α, SubAlgebraMap R α where

section

variable [Zero α] [Add α] [Mul α] [SMul R α]

instance : SetLike (NonUnitalSubalgebra R α) α where
instance : IsMemSMul (NonUnitalSubalgebra R α) R α where
instance : IsMemAdd (NonUnitalSubalgebra R α) α where
instance : IsMemMul (NonUnitalSubalgebra R α) α where
instance : IsMemZero (NonUnitalSubalgebra R α) α where

end

section

variable [SetLike S α]
  [AddMonoidOps α] [Mul α] [IsNonUnitalNonAssocSemiring α]
  [AddMonoidOps R] [Mul R] [IsNonUnitalNonAssocSemiring R]
  [SMul R α] [IsNonUnitalAlgebra R α]
  [IsMemZero S α] [IsMemAdd S α] [IsMemMul S α] [IsMemSMul S R α]
  (s: S)

instance : IsNonUnitalAlgebra R s where
  smul_compat r s a b := by ext; apply smul_compat r s a.val b.val
  smul_zero r := by ext; apply smul_zero

end

section

variable [SemiringOps R] [SemiringOps α] [AlgebraMap R α]
   [SemiringOps β] [AlgebraMap R β]

def mem_algebraMap [SetLike S α] [IsMemAlgebraMap S R α] (s: S) : MemAlgebraMap R s :=
  IsMemAlgebraMap.mem_algebraMap _

instance : SetLike (SubAlgebraMap R α) α where
instance : IsMemAlgebraMap (SubAlgebraMap R α) R α where

instance : SetLike (Subalgebra R α) α where
instance : IsMemAlgebraMap (Subalgebra R α) R α where
instance : IsMemAdd (Subalgebra R α) α where
instance : IsMemMul (Subalgebra R α) α where
instance : IsMemZero (Subalgebra R α) α where
  mem_zero s := by
    show 0 ∈ s
    rw [←map_zero (algebraMap R)]
    apply mem_algebraMap
instance : IsMemOne (Subalgebra R α) α where
  mem_one s := by
    show 1 ∈ s
    rw [←map_one (algebraMap R)]
    apply mem_algebraMap

variable [SetLike S α] [IsSemiring R] [IsSemiring α] [SMul R α] [IsAlgebra R α]
  [IsMemZero S α] [IsMemOne S α] [IsMemAdd S α] [IsMemMul S α] [IsMemAlgebraMap S R α]
  (s: S)

instance [IsMemAlgebraMap S R α] : IsMemSMul S R α where
  mem_smul := by
    intro s r a h
    rw [smul_def]
    apply mem_mul
    apply mem_algebraMap
    assumption

instance : AlgebraMap R s where
  toAlgebraMap := {
    toFun r := {
      val := algebraMap R r
      property := mem_algebraMap s r
    }
    map_zero := by
      show Subtype.mk _ _ = Subtype.mk _ _
      congr; rw [map_zero]
    map_one := by
      show Subtype.mk _ _ = Subtype.mk _ _
      congr; rw [map_one]
    map_add a b := by
      show Subtype.mk _ _ = Subtype.mk _ _; dsimp
      congr; rw [map_add]
    map_mul a b := by
      show Subtype.mk _ _ = Subtype.mk _ _; dsimp
      congr; rw [map_mul]
  }

instance : IsAlgebra R s where
  smul_def _ _ := by ext; apply smul_def
  commutes _ _ := by ext; apply commutes

end

namespace NonUnitalSubalgebra

variable [Zero α] [Add α] [Mul α] [SMul R α]
variable [Zero β] [Add β] [Mul β] [SMul R β]

inductive Closure (R: Type*) [SMul R α] (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure R U a
| zero : Closure R U 0
| add ⦃a b: α⦄ : Closure R U a -> Closure R U b -> Closure R U (a + b)
| mul ⦃a b: α⦄ : Closure R U a -> Closure R U b -> Closure R U (a * b)
| smul (r: R) {a: α} : Closure R U a -> Closure R U (r • a)

def span (R: Type*) [SMul R α] (U: Set α) : NonUnitalSubalgebra R α where
  toSet := Set.ofMem (Closure R U)
  mem_zero := Closure.zero
  mem_add := Closure.add
  mem_mul := Closure.mul
  mem_smul := Closure.smul

def sub_span (U: Set α) : U ⊆ span R U := by
  intro a
  apply Closure.of

def of_mem_span [SetLike S α] [IsMemZero S α] [IsMemMul S α] [IsMemAdd S α] [IsMemSMul S R α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ span R U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | mul a b iha ihb =>
    apply mem_mul <;> assumption
  | smul a b iha =>
    apply mem_smul <;> assumption

instance : Top (NonUnitalSubalgebra R α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ _ _ := True.intro
    mem_mul _ _ _ _ := True.intro
    mem_smul _ _ _ := True.intro
  }

def mem_top (a: α) : a ∈ (⊤: NonUnitalSubalgebra R α) := True.intro
def sub_top (a: NonUnitalSubalgebra R α) : a ⊆ ⊤ := fun _ _ => True.intro

instance [IsLawfulZeroAdd α] [IsLawfulZeroMul α] [IsLawfulSMulZero R α] : Bot (NonUnitalSubalgebra R α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add := by
      rintro _ _ ha hb
      simp [Set.coe_mem] at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [add_zero]; rfl
    mem_mul := by
      rintro _ _ ha hb
      simp [Set.coe_mem] at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [mul_zero]; rfl
    mem_smul := by
      rintro _ _ ha
      simp [Set.coe_mem] at ha
      obtain ⟨a, rfl⟩ := ha
      rw [smul_zero]; rfl
  }

def bot_sub [IsLawfulZeroAdd α] [IsLawfulZeroMul α] [IsLawfulSMulZero R α] (a: NonUnitalSubalgebra R α) : ⊥ ⊆ a := by
  rintro x rfl
  apply mem_zero a

@[simp] def closure_bot_eq_bot [IsLawfulZeroAdd α] [IsLawfulZeroMul α] [IsLawfulSMulZero R α]: span R (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_span _ _ _ h
  nofun

variable [Zero R] [IsLawfulZeroSMul R α] [IsLawfulZeroSMul R β]
   [IsLawfulZeroAdd β] [IsLawfulZeroMul β] [IsLawfulSMulZero R β]

def preimage (f: α →ₐ₀[R] β) (U: NonUnitalSubalgebra R β) : NonUnitalSubalgebra R α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_add := MemAdd.preimage f _
  mem_mul := MemMul.preimage f _
  mem_smul := MemSMul.preimage f _

def image (f: α →ₐ₀[R] β) (U: NonUnitalSubalgebra R α) : NonUnitalSubalgebra R β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_add := MemAdd.image f _
  mem_mul := MemMul.image f _
  mem_smul := MemSMul.image f _

def kernel (f: α →ₐ₀[R] β) : NonUnitalSubalgebra R α := preimage f ⊥

end NonUnitalSubalgebra

namespace Subalgebra

variable [SemiringOps R] [SemiringOps α] [AlgebraMap R α]
   [SemiringOps β] [AlgebraMap R β]

inductive Closure (R: Type*) [SemiringOps R] [AlgebraMap R α] (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure R U a
| add ⦃a b: α⦄ : Closure R U a -> Closure R U b -> Closure R U (a + b)
| mul ⦃a b: α⦄ : Closure R U a -> Closure R U b -> Closure R U (a * b)
| algebraMap ⦃r: R⦄ : Closure R U (algebraMap R r)

def span (R: Type*) [SemiringOps R] [AlgebraMap R α] (U: Set α) : Subalgebra R α where
  toSet := Set.ofMem (Closure R U)
  mem_add := Closure.add
  mem_mul := Closure.mul
  mem_algebraMap := Closure.algebraMap

def sub_span (U: Set α) : U ⊆ span R U := by
  intro a
  apply Closure.of

def of_mem_span [SetLike S α] [IsMemMul S α] [IsMemAdd S α] [IsMemAlgebraMap S R α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ span R U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | algebraMap => apply mem_algebraMap
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | mul a b iha ihb =>
    apply mem_mul <;> assumption

instance : Top (Subalgebra R α) where
  top := {
    toSet := ⊤
    mem_algebraMap _ := True.intro
    mem_add _ _ _ _ := True.intro
    mem_mul _ _ _ _ := True.intro
  }

def mem_top (a: α) : a ∈ (⊤: Subalgebra R α) := True.intro
def sub_top (a: Subalgebra R α) : a ⊆ ⊤ := fun _ _ => True.intro

instance : Bot (Subalgebra R α) where
  bot := {
    toSet := Set.range (algebraMap R)
    mem_algebraMap _ := Set.mem_range'
    mem_add := by
      rintro _ _ ha hb
      simp [Set.coe_mem] at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←map_add]
      apply Set.mem_range'
    mem_mul := by
      rintro _ _ ha hb
      simp [Set.coe_mem] at ha hb
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨b, rfl⟩ := hb
      rw [←map_mul]
      apply Set.mem_range'
  }

def bot_sub (a: Subalgebra R α) : ⊥ ⊆ a := by
  rintro x ⟨_, _, rfl⟩
  apply mem_algebraMap a

@[simp] def closure_bot_eq_bot: span R (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_span _ _ _ h
  nofun

variable [IsSemiring R] [IsSemiring α] [SMul R α] [IsAlgebra R α]
   [IsSemiring β] [SMul R β] [IsAlgebra R β]

def MemAlgebraMap.preimage [SetLike S β]
  [IsMemAlgebraMap S R β] [FunLike F α β]
  [IsOneHom F α β] [IsMulHom F α β] [IsSMulHom F R α β]
  (f: F) (U: S) : MemAlgebraMap R (Set.preimage f U) := by
    intro r
    show f (algebraMap R r) ∈ U
    rw [map_algebraMap]
    apply mem_algebraMap

def MemAlgebraMap.image [SetLike S α]
  [IsMemAlgebraMap S R α] [FunLike F α β]
  [IsOneHom F α β] [IsMulHom F α β] [IsSMulHom F R α β]
  (f: F) (U: S) : MemAlgebraMap R (Set.image f U) := by
    rintro r
    rw [←map_algebraMap f]
    apply Set.mem_image'
    apply mem_algebraMap U

def preimage (f: α →ₐ[R] β) (U: Subalgebra R β) : Subalgebra R α where
  toSet := Set.preimage f U
  mem_algebraMap := MemAlgebraMap.preimage f _
  mem_add := MemAdd.preimage f _
  mem_mul := MemMul.preimage f _

def image (f: α →ₐ[R] β) (U: Subalgebra R α) : Subalgebra R β where
  toSet := Set.image f U
  mem_algebraMap := MemAlgebraMap.image f _
  mem_add := MemAdd.image f _
  mem_mul := MemMul.image f _

def kernel (f: α →ₐ[R] β) : Subalgebra R α := preimage f ⊥

end Subalgebra
