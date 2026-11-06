module

public import Math.Algebra.Monoid.Set.Defs
public import Math.Algebra.Group.Defs

namespace Math

public abbrev MemInv [Inv α] [SetLike S α] (s: S) : Prop :=
  ∀{a: α}, a ∈ s -> a⁻¹ ∈ s

public abbrev MemNeg [Neg α] [SetLike S α] (s: S) : Prop :=
  ∀{a: α}, a ∈ s -> -a ∈ s

public class IsMemInv (S α: Type*) [SetLike S α] [Inv α] where
  mem_inv (s: S) : MemInv s := by intro s; exact s.mem_inv
public class IsMemNeg (S α: Type*) [SetLike S α] [Neg α] where
  mem_neg (s: S) : MemNeg s := by intro s; exact s.mem_neg

export IsMemInv (mem_inv)
export IsMemNeg (mem_neg)

public structure Subgroup (α: Type*) [One α] [Inv α] [Mul α] extends Submonoid α where
  protected mem_inv : MemInv toSet
public structure AddSubgroup (α: Type*) [Zero α] [Neg α] [Add α] extends AddSubmonoid α where
  protected mem_neg : MemNeg toSet

public instance [One α] [Inv α] [Mul α] : SetLike (Subgroup α) α where
public instance [Zero α] [Neg α] [Add α] : SetLike (AddSubgroup α) α where

public instance [One α] [Inv α] [Mul α] : IsMemOne (Subgroup α) α where
public instance [One α] [Inv α] [Mul α] : IsMemInv (Subgroup α) α where
public instance [One α] [Inv α] [Mul α] : IsMemMul (Subgroup α) α where
public instance [Zero α] [Neg α] [Add α] : IsMemZero (AddSubgroup α) α where
public instance [Zero α] [Neg α] [Add α] : IsMemNeg (AddSubgroup α) α where
public instance [Zero α] [Neg α] [Add α] : IsMemAdd (AddSubgroup α) α where

namespace MemInv

public theorem copy [Inv α] [SetLike S α] [IsMemInv S α]
  (u: Set α) (h: ∃s: S, u = s) : MemInv u:= by
  obtain ⟨s, rfl⟩ := h
  exact mem_inv s

public theorem copy' [Inv α] [SetLike S α] [IsMemInv S α]
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemInv u:= by
  intro a ha
  apply (h _).mp
  apply mem_inv
  apply (h _).mpr; assumption

variable [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]
  [Funlike F α β] [IsMulHom F α β] [IsOneHom F α β]

public theorem preimage [SetLike S β] [IsMemInv S β] (f: F) (s: S) : MemInv (Set.preimage f s) := by
  intro a ha
  show f _ ∈ s; rw [map_inv]
  apply mem_inv <;> assumption

public theorem image [SetLike S α] [IsMemInv S α] (f: F) (s: S) : MemInv (Set.image f s) := by
  intro a ha; simp at *
  obtain ⟨a, ha, rfl⟩ := ha
  exists a⁻¹
  apply And.intro
  exact mem_inv s ha
  rw [map_inv]

end MemInv

namespace MemNeg

public theorem copy [Neg α] [SetLike S α] [IsMemNeg S α]
  (u: Set α) (h: ∃s: S, u = s) : MemNeg u:= by
  obtain ⟨s, rfl⟩ := h
  exact mem_neg s

public theorem copy' [Neg α] [SetLike S α] [IsMemNeg S α]
  {s: S} {u: Set α} (h: ∀x, x ∈ s ↔ x ∈ u) : MemNeg u:= by
  intro a ha
  apply (h _).mp
  apply mem_neg
  apply (h _).mpr; assumption

variable [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β]
  [Funlike F α β] [IsAddHom F α β] [IsZeroHom F α β]

public theorem preimage [SetLike S β] [IsMemNeg S β] (f: F) (s: S) : MemNeg (Set.preimage f s) := by
  intro a ha
  show f _ ∈ s; rw [map_neg]
  apply mem_neg <;> assumption

public theorem image [SetLike S α] [IsMemNeg S α] (f: F) (s: S) : MemNeg (Set.image f s) := by
  intro a ha; simp at *
  obtain ⟨a, ha, rfl⟩ := ha
  exists -a
  apply And.intro
  exact mem_neg s ha
  rw [map_neg]

end MemNeg

namespace Subgroup

variable [One α] [Inv α] [Mul α]

inductive Closure [Mul α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| one : Closure U 1
| inv {a: α} : Closure U a -> Closure U (a⁻¹)
| mul {a b: α} : Closure U a -> Closure U b -> Closure U (a * b)

public def closure (U: Set α) : Subgroup α where
  toSet := { Mem := Closure U }
  mem_one := Closure.one
  mem_inv := Closure.inv
  mem_mul := Closure.mul

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemOne S α] [IsMemInv S α] [IsMemMul S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | one => apply mem_one
  | inv => apply mem_inv <;> assumption
  | mul => apply mem_mul <;> assumption

public instance : Top (Subgroup α) where
   top := {
    toSet := ⊤
    mem_one := True.intro
    mem_inv _ := True.intro
    mem_mul _ _ := True.intro
   }

public instance [IsLawfulOne α] [IsLawfulOneInv α] : Bot (Subgroup α) where
   bot := {
    toSet := {1}
    mem_one := rfl
    mem_inv {a} := by
      intro rfl; rw [one_inv]; rfl
    mem_mul {a b} := by
      intro rfl rfl; rw [mul_one]; rfl
   }

public theorem bot_sub [IsLawfulOne α] [IsLawfulOneInv α] (a: Subgroup α) : ⊥ ⊆ a := by intro x rfl; exact mem_one a
public theorem sub_top (a: Subgroup α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemOne S α] [IsMemInv S α] [IsMemMul S α]

@[expose] public def of (s: S) : Subgroup α where
  toSet := s
  mem_one := mem_one s
  mem_inv := mem_inv s
  mem_mul := mem_mul s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : Subgroup α where
  toSet := u
  mem_one := MemOne.copy' hu
  mem_inv := MemInv.copy' hu
  mem_mul := MemMul.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

variable {α β: Type*} [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]
  [Funlike F α β] [IsMulHom F α β] [IsOneHom F α β]

@[expose] public def preimage (f: F) (s: Subgroup β) : Subgroup α where
  toSet := Set.preimage f s
  mem_one := MemOne.preimage f s
  mem_inv := MemInv.preimage f s
  mem_mul := MemMul.preimage f s
@[expose] public def image (f: F) (s: Subgroup α) : Subgroup β where
  toSet := Set.image f s
  mem_one := MemOne.image f s
  mem_inv := MemInv.image f s
  mem_mul := MemMul.image f s

@[simp] public theorem mem_preimage {f: F} {s: Subgroup β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: Subgroup α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end Subgroup

namespace AddSubgroup

variable [Zero α] [Neg α] [Add α]

inductive Closure [Add α] (U: Set α) : α -> Prop where
| of {a: α} : a ∈ U -> Closure U a
| zero : Closure U 0
| neg {a: α} : Closure U a -> Closure U (-a)
| add {a b: α} : Closure U a -> Closure U b -> Closure U (a + b)

public def closure (U: Set α) : AddSubgroup α where
  toSet := { Mem := Closure U }
  mem_zero := Closure.zero
  mem_neg := Closure.neg
  mem_add := Closure.add

public theorem sub_closure {U: Set α} : U ⊆ closure U := fun _ => Closure.of
public theorem of_mem_closure [SetLike S α] [IsMemZero S α] [IsMemNeg S α] [IsMemAdd S α]
  (U: Set α) (s: S) (h: U ⊆ s) : ∀x ∈ closure U, x ∈ s := by
  intro x hx
  induction hx with
  | of => apply h; assumption
  | zero => apply mem_zero
  | neg => apply mem_neg <;> assumption
  | add => apply mem_add <;> assumption

public instance : Top (AddSubgroup α) where
   top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_neg _ := True.intro
    mem_add _ _ := True.intro
   }

public instance [IsLawfulZero α] [IsLawfulNegZero α] : Bot (AddSubgroup α) where
   bot := {
    toSet := {0}
    mem_zero := rfl
    mem_neg {a} := by
      intro rfl; rw [neg_zero]; rfl
    mem_add {a b} := by
      intro rfl rfl; rw [add_zero]; rfl
   }

public theorem bot_sub [IsLawfulZero α] [IsLawfulNegZero α] (a: AddSubgroup α) : ⊥ ⊆ a := by intro x rfl; exact mem_zero a
public theorem sub_top (a: AddSubgroup α) : a ⊆ ⊤ := fun _ _ => True.intro

section

variable [SetLike S α] [IsMemZero S α] [IsMemNeg S α] [IsMemAdd S α]

@[expose] public def of (s: S) : AddSubgroup α where
  toSet := s
  mem_zero := mem_zero s
  mem_neg := mem_neg s
  mem_add := mem_add s
@[expose] public def copy (s: S) (u: Set α) (hu: ∀x, x ∈ s ↔ x ∈ u) : AddSubgroup α where
  toSet := u
  mem_zero := MemZero.copy' hu
  mem_neg := MemNeg.copy' hu
  mem_add := MemAdd.copy' hu

@[simp] public theorem mem_of {s: S} : ∀{x}, x ∈ of s ↔ x ∈ s := Iff.rfl
@[simp] public theorem mem_copy {s: S} {u: Set α} {hu} : ∀{x}, x ∈ copy s u hu ↔ x ∈ s := (hu _).symm

end

variable {α β: Type*} [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β]
  [Funlike F α β] [IsAddHom F α β] [IsZeroHom F α β]

@[expose] public def preimage (f: F) (s: AddSubgroup β) : AddSubgroup α where
  toSet := Set.preimage f s
  mem_zero := MemZero.preimage f s
  mem_neg := MemNeg.preimage f s
  mem_add := MemAdd.preimage f s
@[expose] public def image (f: F) (s: AddSubgroup α) : AddSubgroup β where
  toSet := Set.image f s
  mem_zero := MemZero.image f s
  mem_neg := MemNeg.image f s
  mem_add := MemAdd.image f s

@[simp] public theorem mem_preimage {f: F} {s: AddSubgroup β} : ∀{x}, x ∈ s.preimage f ↔ f x ∈ s := Iff.rfl
@[simp] public theorem mem_image {f: F} {s: AddSubgroup α} : ∀{x}, x ∈ s.image f ↔ ∃i, i ∈ s ∧ f i = x := Set.mem_image

end AddSubgroup

variable {S α: Type*} [SetLike S α]

public instance [Neg α] [IsMemNeg S α] : IsMemInv (MulOfAdd S) (MulOfAdd α) where
  mem_inv := mem_neg (S := S) (α := α)
public instance [Inv α] [IsMemInv S α] : IsMemNeg (AddOfMul S) (AddOfMul α) where
  mem_neg := mem_inv (S := S) (α := α)

public theorem mem_powz
  [GroupOps α] [IsGroup α]
  [IsMemOne S α] [IsMemInv S α] [IsMemMul S α]
  (a: α) (n: ℤ) (s: S) : a ∈ s -> a ^ n ∈ s := by
  intro h
  cases n with
  | ofNat n => dsimp; rw [powz_ofNat]; apply mem_pown; assumption
  | negSucc n => rw [powz_negSucc]; apply mem_inv; apply mem_pown; assumption

public theorem mem_div
  [Inv α] [Mul α] [Div α] [IsLawfulDiv α]
  [IsMemInv S α] [IsMemMul S α]
  (a b: α) (s: S) : a ∈ s -> b ∈ s -> a / b ∈ s := by
  intro ha hb; rw [div_eq_mul_inv]
  apply mem_mul; assumption
  apply mem_inv; assumption

public theorem mem_zsmul
  [AddGroupOps α] [IsAddGroup α]
  [IsMemZero S α] [IsMemZero S α] [IsMemNeg S α] [IsMemAdd S α]
  (a: α) (n: ℤ) (s: S) : a ∈ s -> n • a ∈ s :=
  mem_powz (S := MulOfAdd S) (α := MulOfAdd α) _ _ _

public theorem mem_sub
  [Neg α] [Add α] [Sub α] [IsLawfulSub α]
  [IsMemNeg S α] [IsMemAdd S α]
  (a b: α) (s: S) : a ∈ s -> b ∈ s -> a - b ∈ s :=
  mem_div (S := MulOfAdd S) (α := MulOfAdd α) _ _ _

public instance [Inv α] [IsMemInv S α] (s: S) : Inv s where
  inv a := {
    val := a.val⁻¹
    property := mem_inv s a.property
  }
public instance [Neg α] [IsMemNeg S α] (s: S) : Neg s where
  neg a := {
    val := -a.val
    property := mem_neg s a.property
  }

@[simp] public theorem subtype_inv [Inv α] [IsMemInv S α] {s: S} (a: (s: Type _)) : (a⁻¹: (s: Type _)).val = a.val⁻¹ := rfl
@[simp] public theorem subtype_neg [Neg α] [IsMemNeg S α] {s: S} (a: (s: Type _)) : (-a: (s: Type _)).val = -a.val := rfl

section

variable [GroupOps α] [IsGroup α] [IsMemOne S α] [IsMemInv S α] [IsMemMul S α]

public instance (s: S) : Pow s ℤ where
  pow a n := {
    val := a.val ^ n
    property := mem_powz _ n s a.property
  }

public instance (s: S) : Div s where
  div a b := {
    val := a.val / b.val
    property := mem_div _ _ s a.property b.property
  }

@[simp] public theorem subtype_powz {s: S} (a: (s: Type _)) (n: ℤ) : (a ^ n).val = a.val ^ n := rfl

public instance (s: S) : IsGroup s where
  div_eq_mul_inv _ _ := by ext; apply div_eq_mul_inv
  powz_ofNat _ _ := by ext; apply powz_ofNat
  powz_negSucc _ _ := by ext; apply powz_negSucc
  inv_mul_cancel _ := by ext; apply inv_mul_cancel

end

section

variable [AddGroupOps α] [IsAddGroup α] [IsMemZero S α] [IsMemNeg S α] [IsMemAdd S α]

public instance (s: S) : SMul ℤ s where
  smul n a := {
    val := n • a.val
    property := mem_zsmul _ n s a.property
  }

public instance (s: S) : Sub s where
  sub a b := {
    val := a.val - b.val
    property := mem_sub _ _ s a.property b.property
  }

@[simp] public theorem subtype_zsmul {s: S} (a: (s: Type _)) (n: ℤ) : (n • a).val = n • a.val := rfl

public instance (s: S) : IsAddGroup s where
  sub_eq_add_neg _ _ := by ext; apply sub_eq_add_neg
  ofNat_zsmul _ _ := by ext; apply ofNat_zsmul
  negSucc_zsmul _ _ := by ext; apply negSucc_zsmul
  neg_add_cancel _ := by ext; apply neg_add_cancel

end
