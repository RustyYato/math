import LeanMath.Algebra.Group.Defs
import LeanMath.Algebra.Monoid.Set

def MemInv [Inv α] [SetLike S α] (s: S) := ∀⦃a: α⦄, a ∈ s -> a⁻¹ ∈ s
def MemNeg [Neg α] [SetLike S α] (s: S) := ∀⦃a: α⦄, a ∈ s -> -a ∈ s

class IsMemInv (S α: Type*) [Inv α] [SetLike S α] where
  protected mem_inv (s: S) : MemInv s := by intro s; exact s.mem_inv

class IsMemNeg (S α: Type*) [Neg α] [SetLike S α] where
  protected mem_neg (s: S) : MemNeg s := by intro s; exact s.mem_neg

def mem_inv [Inv α] [SetLike S α] [IsMemInv S α] (s: S): MemInv s :=
  IsMemInv.mem_inv _

def mem_neg [Neg α] [SetLike S α] [IsMemNeg S α] (s: S): MemNeg s :=
  IsMemNeg.mem_neg _

structure SubInv (α: Type*) [Inv α] where
  toSet: Set α
  protected mem_inv : MemInv toSet

structure SubNeg (α: Type*) [Neg α] where
  toSet: Set α
  protected mem_neg : MemNeg toSet

instance [Inv α] : SetLike (SubInv α) α where
instance [Inv α] : IsMemInv (SubInv α) α where

instance [Neg α] : SetLike (SubNeg α) α where
instance [Neg α] : IsMemNeg (SubNeg α) α where

structure Subgroup (α: Type*) [Mul α] [Inv α] [One α] extends SubMonoid α, SubInv α where

structure AddSubgroup (α: Type*) [Add α] [Neg α] [Zero α] extends AddSubMonoid α, SubNeg α where

instance [Mul α] [Inv α] [One α] : SetLike (Subgroup α) α where
instance [Mul α] [Inv α] [One α] : IsMemMul (Subgroup α) α where
instance [Mul α] [Inv α] [One α] : IsMemInv (Subgroup α) α where
instance [Mul α] [Inv α] [One α] : IsMemOne (Subgroup α) α where

instance [Add α] [Neg α] [Zero α] : SetLike (AddSubgroup α) α where
instance [Add α] [Neg α] [Zero α] : IsMemAdd (AddSubgroup α) α where
instance [Add α] [Neg α] [Zero α] : IsMemNeg (AddSubgroup α) α where
instance [Add α] [Neg α] [Zero α] : IsMemZero (AddSubgroup α) α where

namespace Subgroup

variable [Mul α] [Mul β] [Inv α] [Inv β] [One α] [One β]

def copy (S: Subgroup α) (U: Set α) (h: ∀x, x ∈ S ↔ x ∈ U) : Subgroup α where
  toSet := U
  mem_one := (h _).mp (mem_one S)
  mem_mul _ _ ha hb := (h _).mp (mem_mul S ((h _).mpr ha) ((h _).mpr hb))
  mem_inv _ ha := (h _).mp (mem_inv S ((h _).mpr ha))


inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| one : Closure U 1
| inv ⦃a: α⦄ : Closure U a -> Closure U (a⁻¹)
| mul ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a * b)

def closure (U: Set α) : Subgroup α where
  toSet := Set.ofMem (Closure U)
  mem_one := Closure.one
  mem_inv := Closure.inv
  mem_mul := Closure.mul

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a ha
  apply Closure.of
  assumption

def of_mem_closure [SetLike S α] [IsMemMul S α] [IsMemInv S α] [IsMemOne S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | one => apply mem_one
  | inv a ih =>
    apply mem_inv <;> assumption
  | mul a b iha ihb =>
    apply mem_mul <;> assumption

instance : Top (Subgroup α) where
  top := {
    toSet := ⊤
    mem_one := True.intro
    mem_inv _ _ := True.intro
    mem_mul _ _ _ _ := True.intro
  }

instance [IsLawfulOneMul α] [IsLawfulOneInv α] : Bot (Subgroup α) where
  bot := {
    toSet := {1}
    mem_one := rfl
    mem_inv := by
      rintro _ rfl
      rw [one_inv]; rfl
    mem_mul := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
  }

def mem_top (a: α) : a ∈ (⊤: Subgroup α) := True.intro
def sub_top (a: Subgroup α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub [IsLawfulOneMul α] [IsLawfulOneInv α] (a: Subgroup α) : ⊥ ⊆ a := by
  rintro _ rfl
  apply mem_one a
@[simp] def closure_bot_eq_bot [IsLawfulOneMul α] [IsLawfulOneInv α] : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

end Subgroup

section

variable [GroupOps α] [GroupOps β] [IsGroup α] [IsGroup β]

def MemInv.preimage [SetLike S β] [IsMemInv S β] [IsMemOne S β] [FunLike F α β] [IsMulHom F α β] [IsOneHom F α β] (f: F) (U: S) : MemInv (Set.preimage f U) := by
    intro a h
    show f _ ∈ U
    rw [map_inv]
    apply mem_inv U
    assumption

def MemInv.image [SetLike S α] [IsMemInv S α] [IsMemOne S α] [FunLike F α β] [IsMulHom F α β] [IsOneHom F α β] (f: F) (U: S) : MemInv (Set.image f U) := by
    rintro _ ⟨a, _, rfl⟩
    show (f _)⁻¹ ∈ _
    rw [←map_inv f]
    apply Set.mem_image'
    apply mem_inv U
    assumption

namespace Subgroup

section

variable [FunLike F α β] [IsOneHom F α β] [IsMulHom F α β]

def preimage (f: F) (U: Subgroup β) : Subgroup α where
  toSet := Set.preimage f U
  mem_one := MemOne.preimage f _
  mem_inv := MemInv.preimage f _
  mem_mul := MemMul.preimage f _

def image (f: F) (U: Subgroup α) : Subgroup β where
  toSet := Set.image f U
  mem_one := MemOne.image f _
  mem_inv := MemInv.image f _
  mem_mul := MemMul.image f _

def range (f: F) : Subgroup β :=
  (Subgroup.image f ⊤).copy (Set.range f) (by
    show ∀_, _ ∈ Set.image _ ⊤ ↔ _
    rw [Set.image_univ_eq_range]
    intro x; apply Iff.rfl)

def kernel (f: F) : Subgroup α := preimage f ⊥

end

noncomputable def equivRange [EmbeddingLike F α β] [IsOneHom F α β] [IsMulHom F α β] (f: F) : α ≃* range f where
  toEquiv := Equiv.ofBij {
    toFun x := {
      val := f x
      property := by apply Set.mem_range'
    }
    inj' := by
      intro a b h
      exact inj f (Subtype.mk.inj h)
    surj' := by
      rintro ⟨b, a, rfl⟩
      exists a
  }
  map_one := by
    dsimp; rw [Equiv.apply_ofBij]
    ext; apply map_one f
  map_mul x y := by
    dsimp; iterate 3 rw [Equiv.apply_ofBij]
    ext; apply map_mul f

end Subgroup

end

namespace AddSubgroup

variable [Add α] [Add β] [Neg α] [Neg β] [Zero α] [Zero β]

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| neg ⦃a: α⦄ : Closure U a -> Closure U (-a)
| add ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a + b)

def closure (U: Set α) : AddSubgroup α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_neg := Closure.neg
  mem_add := Closure.add

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a
  apply Closure.of

def of_mem_closure [SetLike S α] [IsMemAdd S α] [IsMemNeg S α] [IsMemZero S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | neg a iha =>
    apply mem_neg <;> assumption
  | add a b iha ihb =>
    apply mem_add <;> assumption

instance : Top (AddSubgroup α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_neg _ _ := True.intro
    mem_add _ _ _ _ := True.intro
  }

instance [IsLawfulZeroAdd α] [IsLawfulNegZero α] : Bot (AddSubgroup α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_neg := by
      rintro _ rfl
      rw [neg_zero]; rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
  }

def mem_top (a: α) : a ∈ (⊤: AddSubgroup α) := True.intro
def sub_top (a: AddSubgroup α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub [IsLawfulZeroAdd α] [IsLawfulNegZero α] (a: AddSubgroup α) : ⊥ ⊆ a := by
  rintro _ rfl
  apply mem_zero a
@[simp] def closure_bot_eq_bot [IsLawfulZeroAdd α] [IsLawfulNegZero α] : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

end AddSubgroup

section

variable [AddGroupOps α] [AddGroupOps β] [IsAddGroup α] [IsAddGroup β]

def MemNeg.preimage [SetLike S β] [IsMemNeg S β] [IsMemZero S β] [FunLike F α β] [IsAddHom F α β] [IsZeroHom F α β] (f: F) (U: S) : MemNeg (Set.preimage f U) := by
    intro a h
    show f _ ∈ U
    rw [map_neg]
    apply mem_neg U
    assumption

def MemNeg.image [SetLike S α] [IsMemNeg S α] [IsMemZero S α] [FunLike F α β] [IsAddHom F α β] [IsZeroHom F α β] (f: F) (U: S) : MemNeg (Set.image f U) := by
    rintro _ ⟨a, _, rfl⟩
    show -(f _) ∈ _
    rw [←map_neg f]
    apply Set.mem_image'
    apply mem_neg U
    assumption

namespace AddSubgroup

def preimage (f: α →+ β) (U: AddSubgroup β) : AddSubgroup α where
  toSet := Set.preimage f U
  mem_zero := MemZero.preimage f _
  mem_neg := MemNeg.preimage f _
  mem_add := MemAdd.preimage f _

def image (f: α →+ β) (U: AddSubgroup α) : AddSubgroup β where
  toSet := Set.image f U
  mem_zero := MemZero.image f _
  mem_neg := MemNeg.image f _
  mem_add := MemAdd.image f _

def kernel (f: α →+ β) : AddSubgroup α := preimage f ⊥

end AddSubgroup

end

variable (s: S) [SetLike S α]

section

instance [Inv α] [IsMemInv S α] : Inv s where
  inv a := {
    val := a.val⁻¹
    property := mem_inv s a.property
  }

instance [Neg α] [IsMemNeg S α] : Neg s where
  neg a := {
    val := -a.val
    property := mem_neg s a.property
  }

instance [Neg α] [IsMemNeg S α] : IsMemInv (MulOfAdd S) (MulOfAdd α) where
  mem_inv a := mem_neg a.get

instance [Inv α] [IsMemInv S α] : IsMemNeg (AddOfMul S) (AddOfMul α) where
  mem_neg a := mem_inv a.get

end

section

variable [GroupOps α] [IsGroup α] [IsMemMul S α] [IsMemInv S α] [IsMemOne S α]

def mem_zpow {a: α} (n: ℤ) : a ∈ s -> a ^ n ∈ s := by
  intro h
  cases n with
  | ofNat n =>
    rw [zpow_ofNat]
    apply mem_npow
    assumption
  | negSucc =>
    rw [zpow_negSucc]
    apply mem_inv
    apply mem_npow
    assumption

def mem_div {a b: α} : a ∈ s -> b ∈ s -> a / b ∈ s := by
  intro h g
  rw [div_eq_mul_inv]
  apply mem_mul
  assumption
  apply mem_inv
  assumption

instance : Pow s ℤ where
  pow a n := {
    val := a.val ^ n
    property := mem_zpow s n a.property
  }

instance : Div s where
  div a b := {
    val := a.val / b.val
    property := mem_div s a.property b.property
  }

instance : IsGroup s where
  div_eq_mul_inv _ _ := by
    apply Subtype.val_inj
    apply div_eq_mul_inv
  zpow_ofNat _ _ := by
    apply Subtype.val_inj
    apply zpow_ofNat
  zpow_negSucc _ _ := by
    apply Subtype.val_inj
    apply zpow_negSucc
  mul_inv_cancel _ := by
    apply Subtype.val_inj
    apply mul_inv_cancel

end

section

variable [AddGroupOps α] [IsAddGroup α] [IsMemAdd S α] [IsMemNeg S α] [IsMemZero S α]

def mem_zsmul {a: α} (n: ℤ) : a ∈ s -> n • a ∈ s :=
  mem_zpow (MulOfAdd.mk s) n

def mem_sub {a b: α} : a ∈ s -> b ∈ s -> a - b ∈ s :=
  mem_div (MulOfAdd.mk s)

instance : SMul ℤ s where
  smul n a := {
    val := n • a.val
    property := mem_zsmul s n a.property
  }

instance : Sub s where
  sub a b := {
    val := a.val - b.val
    property := mem_sub s a.property b.property
  }

instance : IsAddGroup s where
  sub_eq_add_neg _ _ := by
    apply Subtype.val_inj
    apply sub_eq_add_neg
  ofNat_zsmul _ _ := by
    apply Subtype.val_inj
    apply ofNat_zsmul
  negSucc_zsmul _ _ := by
    apply Subtype.val_inj
    apply negSucc_zsmul
  add_neg_cancel _ := by
    apply Subtype.val_inj
    apply add_neg_cancel

end
