import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Algebra.Monoid.Set
import LeanMath.Data.Set.Defs

def MemSMul [SetLike S α] (R: Type*) [SMul R α] (s: S) :=
  ∀(r: R) {a: α}, a ∈ s -> r • a ∈ s

class IsMemSMul (S R α: Type*) [SetLike S α] [SMul R α] where
  protected mem_smul (s: S) : MemSMul R s := by intro s; exact s.mem_smul

def mem_smul [SetLike S α] [SMul R α] [IsMemSMul S R α] (s: S) : MemSMul R s :=
  IsMemSMul.mem_smul s

structure SubSMul (R α: Type*) [SMul R α] where
  toSet: Set α
  protected mem_smul : MemSMul R toSet

instance [SMul R α] : SetLike (SubSMul R α) α where
instance [SMul R α] : IsMemSMul (SubSMul R α) R α where

structure Submodule (R α: Type*) [Zero α] [Add α] [SMul R α] extends SubSMul R α, AddSubMonoid α where

instance [Zero α] [Add α] [SMul R α] : SetLike (Submodule R α) α where
instance [Zero α] [Add α] [SMul R α] : IsMemZero (Submodule R α) α where
instance [Zero α] [Add α] [SMul R α] : IsMemAdd (Submodule R α) α where
instance [Zero α] [Add α] [SMul R α] : IsMemSMul (Submodule R α) R α where

variable (s: S) [SetLike S α] [SMul R α] [SMul R β]
variable [IsMemSMul S R α] [MonoidOps R] [IsMonoid R]

namespace Submodule

variable [Zero α] [Add α] [IsMemAdd S α] [IsMemZero S α]
variable [Zero β] [Add β]

inductive Span (R: Type*) [SMul R α] (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Span R U a
| zero : Span R U 0
| add ⦃a b: α⦄ : Span R U a -> Span R U b -> Span R U (a + b)
| smul (r: R) {a: α} : Span R U a -> Span R U (r • a)

def span (R: Type*) [SMul R α] (U: Set α) : Submodule R α where
  toSet := Set.ofMem (Span R U)
  mem_zero := Span.zero
  mem_add := Span.add
  mem_smul := Span.smul

def sub_span (U: Set α) : U ⊆ span R U := by
  intro a
  apply Span.of

def of_mem_span (U: Set α) (s: S) : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ span R U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | smul r a iha =>
    apply mem_smul <;> assumption

instance : Top (Submodule R α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_add _ _ _ _ := True.intro
    mem_smul _ _ _ := True.intro
  }

variable [IsLawfulZeroAdd α] [IsLawfulSMulZero R α]

instance : Bot (Submodule R α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_add := by
      intro a b rfl rfl
      rw [add_zero]; rfl
    mem_smul := by
      intro r a rfl
      rw [smul_zero]
      rfl
  }

def mem_top (a: α) : a ∈ (⊤: Submodule R α) := True.intro
def sub_top (a: Submodule R α) : a ⊆ ⊤ := fun _ _ => True.intro

def bot_sub (a: Submodule R α) : ⊥ ⊆ a := by
  rintro x rfl
  apply mem_zero a

@[simp] def closure_bot_eq_bot : span R (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_span _ _ _ h
  nofun

def MemSMul.preimage [SetLike S β] [IsMemSMul S R β] [FunLike F α β] [IsSMulHom F R α β]
  (f: F) (U: S) : MemSMul R (Set.preimage f U) := by
    intro r a ha
    show f (r • a) ∈ U
    rw [map_smul]
    apply mem_smul
    assumption

def MemSMul.image [SetLike S α] [IsMemSMul S R α] [FunLike F α β] [IsSMulHom F R α β]
  (f: F) (U: S) : MemSMul R (Set.image f U) := by
    rintro r a ⟨a, _, rfl⟩
    rw [←map_smul]
    apply Set.mem_image'
    apply mem_smul U r
    assumption

variable [Zero R] [IsLawfulZeroSMul R α] [IsLawfulZeroSMul R β]

def preimage (f: α →ₗ[R] β) (U: Submodule R β) : Submodule R α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_add := MemAdd.preimage f _
  mem_smul := MemSMul.preimage f _

def image (f: α →ₗ[R] β) (U: Submodule R α) : Submodule R β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_add := MemAdd.image f _
  mem_smul := MemSMul.image f _

variable [IsLawfulZeroAdd β] [IsLawfulSMulZero R β]

def kernel (f: α →ₗ[R] β) : Submodule R α := preimage f ⊥

def IsSpanningSet (R: Type*) [SMul R α] (U: Set α) : Prop := ∀x, x ∈ span R U

end Submodule

instance : SMul R s where
  smul r a := {
    val := r • a.val
    property := mem_smul s r a.property
  }

instance [IsMonoidAction R α] : IsMonoidAction R s where
  one_smul _ := by
    apply Subtype.val_inj
    apply one_smul
  mul_smul _ _ _ := by
    apply Subtype.val_inj
    apply mul_smul

variable [AddMonoidOps α] [IsAddMonoid α] [IsMemZero S α] [IsMemAdd S α]

instance [IsDistributiveAction R α] : IsDistributiveAction R s where
  smul_zero r := by
    apply Subtype.val_inj
    apply smul_zero
  smul_add _ _ _ := by
    apply Subtype.val_inj
    apply smul_add
