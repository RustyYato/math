import LeanMath.Algebra.Monoid.Action.Defs
import LeanMath.Algebra.Monoid.Set
import LeanMath.Data.Set.Defs

class IsMemSMul (S R α: Type*) [SetLike S α] [SMul R α] where
  protected mem_smul (s: S) (r: R) {a: α} : a ∈ s -> r • a ∈ s := by intro s; exact s.mem_smul

def mem_smul [SetLike S α] [SMul R α] [IsMemSMul S R α] (s: S) (r: R) {a: α} : a ∈ s -> r • a ∈ s :=
  IsMemSMul.mem_smul _ _

structure SubSMul (R α: Type*) [SMul R α] where
  toSet: Set α
  protected mem_smul (r: R) {a: α} : a ∈ toSet -> r • a ∈ toSet

instance [SMul R α] : SetLike (SubSMul R α) α where
instance [SMul R α] : IsMemSMul (SubSMul R α) R α where

structure Submodule (R α: Type*) [Zero α] [Add α] [SMul R α] extends SubSMul R α, AddSubMonoid α where

instance [Zero α] [Add α] [SMul R α] : SetLike (Submodule R α) α where
instance [Zero α] [Add α] [SMul R α] : IsMemZero (Submodule R α) α where
instance [Zero α] [Add α] [SMul R α] : IsMemAdd (Submodule R α) α where
instance [Zero α] [Add α] [SMul R α] : IsMemSMul (Submodule R α) R α where

variable (s: S) [SetLike S α] [SMul R α] [IsMemSMul S R α]
variable [MonoidOps R] [IsMonoid R]

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
