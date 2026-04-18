import LeanMath.Algebra.Group.Set

def MemConj [GroupOps α] [IsGroup α] [SetLike S α] (s: S) := ∀⦃a x: α⦄, a ∈ s -> conj x a ∈ s
def MemAddConj [AddGroupOps α] [IsAddGroup α] [SetLike S α] (s: S) := ∀⦃a x: α⦄, a ∈ s -> add_conj x a ∈ s

class IsMemConj (S α: Type*) [GroupOps α] [IsGroup α] [SetLike S α] where
  protected mem_conj (s: S) : MemConj s := by intro s; exact s.mem_conj

class IsMemAddConj (S α: Type*) [AddGroupOps α] [IsAddGroup α] [SetLike S α] where
  protected mem_add_conj (s: S) : MemAddConj s := by intro s; exact s.mem_add_conj

def mem_conj [GroupOps α] [IsGroup α] [SetLike S α] [IsMemConj S α] (s: S) : MemConj s := IsMemConj.mem_conj _
def mem_add_conj [AddGroupOps α] [IsAddGroup α] [SetLike S α] [IsMemAddConj S α] (s: S) : MemAddConj s := IsMemAddConj.mem_add_conj _

structure NormalSubgroup (α: Type*) [GroupOps α] [IsGroup α] extends Subgroup α where
  protected mem_conj : MemConj toSet

structure NormalAddSubgroup (α: Type*) [AddGroupOps α] [IsAddGroup α] extends AddSubgroup α where
  protected mem_add_conj : MemAddConj toSet

namespace NormalSubgroup

variable [GroupOps α] [IsGroup α] [GroupOps β] [IsGroup β]
   [FunLike F α β] [IsMulHom F α β] [IsOneHom F α β]

instance : SetLike (NormalSubgroup α) α where
instance : IsMemOne (NormalSubgroup α) α where
instance : IsMemMul (NormalSubgroup α) α where
instance : IsMemInv (NormalSubgroup α) α where
instance : IsMemConj (NormalSubgroup α) α where

def MemConj.preimage [SetLike S β] [IsMemConj S β] (f: F) (U: S) : MemConj (Set.preimage f U) := by
    intro a h
    simp
    intro g
    rw [map_mul, map_mul, map_inv]
    apply mem_conj U
    assumption

def MemConj.image [SetLike S α] [IsMemConj S α] (f: F) (hf: Function.Surjective f) (U: S) : MemConj (Set.image f U) := by
    rintro _ x ⟨a, _, rfl⟩
    dsimp
    obtain ⟨x, rfl⟩ := hf x
    rw [←map_inv, ←map_mul, ←map_mul]
    apply Set.mem_image'
    apply mem_conj U
    assumption

def copy (S: NormalSubgroup α) (U: Set α) (h: ∀x, x ∈ S ↔ x ∈ U) : NormalSubgroup α where
  toSet := U
  mem_one := (h _).mp (mem_one S)
  mem_mul _ _ ha hb := (h _).mp (mem_mul S ((h _).mpr ha) ((h _).mpr hb))
  mem_inv _ ha := (h _).mp (mem_inv S ((h _).mpr ha))
  mem_conj _ _ ha := (h _).mp (mem_conj S ((h _).mpr ha))

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| one : Closure U 1
| inv ⦃a: α⦄ : Closure U a -> Closure U (a⁻¹)
| mul ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a * b)
| conj ⦃a x: α⦄ : Closure U a -> Closure U (conj x a)

def closure (U: Set α) : NormalSubgroup α where
  toSet := Set.ofMem (Closure U)
  mem_one := Closure.one
  mem_inv := Closure.inv
  mem_mul := Closure.mul
  mem_conj := Closure.conj

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a ha
  apply Closure.of
  assumption

def of_mem_closure [SetLike S α] [IsMemMul S α] [IsMemInv S α] [IsMemOne S α] [IsMemConj S α] (U: Set α) (s: S)
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
  | conj a ih =>
    apply mem_conj <;> assumption

instance : Top (NormalSubgroup α) where
  top := {
    toSet := ⊤
    mem_one := True.intro
    mem_inv _ _ := True.intro
    mem_mul _ _ _ _ := True.intro
    mem_conj _ _ _ := True.intro
  }

instance : Bot (NormalSubgroup α) where
  bot := {
    toSet := {1}
    mem_one := rfl
    mem_inv := by
      rintro _ rfl
      rw [one_inv]; rfl
    mem_mul := by
      rintro _ _ rfl rfl
      rw [mul_one]; rfl
    mem_conj := by
      intro a x rfl
      rw [map_one]; rfl
  }

def mem_top (a: α) : a ∈ (⊤: NormalSubgroup α) := True.intro
def sub_top (a: NormalSubgroup α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub (a: NormalSubgroup α) : ⊥ ⊆ a := by
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

def preimage [FunLike F α β] [IsMulHom F α β] [IsOneHom F α β] (f: F) (U: NormalSubgroup β) : NormalSubgroup α where
  toSet := U.toSet.preimage f
  mem_one := MemOne.preimage _ U
  mem_inv := MemInv.preimage _ U
  mem_mul := MemMul.preimage _ U
  mem_conj := MemConj.preimage _ U

def image (f: F) (hf: Function.Surjective f) (U: NormalSubgroup α) : NormalSubgroup β where
  toSet := U.toSet.image f
  mem_one := MemOne.image _ U
  mem_inv := MemInv.image _ U
  mem_mul := MemMul.image _ U
  mem_conj := MemConj.image _ hf U

def range (f: F) (hf: Function.Surjective f) : NormalSubgroup β :=
  (NormalSubgroup.image f hf ⊤).copy (Set.range f) (by
    show ∀_, _ ∈ Set.image _ ⊤ ↔ _
    rw [Set.image_univ_eq_range]
    intro x; apply Iff.rfl)

def kernel (f: F) : NormalSubgroup α := preimage f ⊥

end NormalSubgroup

namespace NormalAddSubgroup

variable [AddGroupOps α] [IsAddGroup α] [AddGroupOps β] [IsAddGroup β]
   [FunLike F α β] [IsAddHom F α β] [IsZeroHom F α β]

instance : SetLike (NormalAddSubgroup α) α where
instance : IsMemZero (NormalAddSubgroup α) α where
instance : IsMemAdd (NormalAddSubgroup α) α where
instance : IsMemNeg (NormalAddSubgroup α) α where
instance : IsMemAddConj (NormalAddSubgroup α) α where

def MemAddConj.preimage [SetLike S β] [IsMemAddConj S β] (f: F) (U: S) : MemAddConj (Set.preimage f U) := by
    intro a h
    simp
    intro g
    rw [map_add, map_add, map_neg]
    apply mem_add_conj U
    assumption

def MemAddConj.image [SetLike S α] [IsMemAddConj S α] (f: F) (hf: Function.Surjective f) (U: S) : MemAddConj (Set.image f U) := by
    rintro _ x ⟨a, _, rfl⟩
    dsimp
    obtain ⟨x, rfl⟩ := hf x
    rw [←map_neg, ←map_add, ←map_add]
    apply Set.mem_image'
    apply mem_add_conj U
    assumption

def copy (S: NormalAddSubgroup α) (U: Set α) (h: ∀x, x ∈ S ↔ x ∈ U) : NormalAddSubgroup α where
  toSet := U
  mem_zero := (h _).mp (mem_zero S)
  mem_add _ _ ha hb := (h _).mp (mem_add S ((h _).mpr ha) ((h _).mpr hb))
  mem_neg _ ha := (h _).mp (mem_neg S ((h _).mpr ha))
  mem_add_conj _ _ ha := (h _).mp (mem_add_conj S ((h _).mpr ha))

inductive Closure (U: Set α) : α -> Prop where
| of (a: α) (h: a ∈ U) : Closure U a
| zero : Closure U 0
| neg ⦃a: α⦄ : Closure U a -> Closure U (-a)
| add ⦃a b: α⦄ : Closure U a -> Closure U b -> Closure U (a + b)
| add_conj ⦃a x: α⦄ : Closure U a -> Closure U (add_conj x a)

def closure (U: Set α) : NormalAddSubgroup α where
  toSet := Set.ofMem (Closure U)
  mem_zero := Closure.zero
  mem_neg := Closure.neg
  mem_add := Closure.add
  mem_add_conj := Closure.add_conj

def sub_closure (U: Set α) : U ⊆ closure U := by
  intro a ha
  apply Closure.of
  assumption

def of_mem_closure [SetLike S α] [IsMemAdd S α] [IsMemNeg S α] [IsMemZero S α] [IsMemAddConj S α] (U: Set α) (s: S)
  : (∀{a}, a ∈ U -> a ∈ s) -> ∀{a}, a ∈ closure U -> a ∈ s := by
  intro g a h
  induction h with
  | of =>
    apply g
    assumption
  | zero => apply mem_zero
  | neg a ih =>
    apply mem_neg <;> assumption
  | add a b iha ihb =>
    apply mem_add <;> assumption
  | add_conj a ih =>
    apply mem_add_conj <;> assumption

instance : Top (NormalAddSubgroup α) where
  top := {
    toSet := ⊤
    mem_zero := True.intro
    mem_neg _ _ := True.intro
    mem_add _ _ _ _ := True.intro
    mem_add_conj _ _ _ := True.intro
  }

instance : Bot (NormalAddSubgroup α) where
  bot := {
    toSet := {0}
    mem_zero := rfl
    mem_neg := by
      rintro _ rfl
      rw [neg_zero]; rfl
    mem_add := by
      rintro _ _ rfl rfl
      rw [add_zero]; rfl
    mem_add_conj := by
      intro a x rfl
      rw [map_zero]; rfl
  }

def mem_top (a: α) : a ∈ (⊤: NormalAddSubgroup α) := True.intro
def sub_top (a: NormalAddSubgroup α) : a ⊆ ⊤ := fun _ _ => True.intro
def bot_sub (a: NormalAddSubgroup α) : ⊥ ⊆ a := by
  rintro _ rfl
  apply mem_zero a
@[simp] def closure_bot_eq_bot : closure (α := α) ⊥ = ⊥ := by
  symm; apply SetLike.ext
  intro a
  apply Iff.intro
  apply bot_sub
  intro h
  apply of_mem_closure _ _ _ h
  nofun

def preimage [FunLike F α β] [IsAddHom F α β] [IsZeroHom F α β] (f: F) (U: NormalAddSubgroup β) : NormalAddSubgroup α where
  toSet := U.toSet.preimage f
  mem_zero := MemZero.preimage _ U
  mem_neg := MemNeg.preimage _ U
  mem_add := MemAdd.preimage _ U
  mem_add_conj := MemAddConj.preimage _ U

def image (f: F) (hf: Function.Surjective f) (U: NormalAddSubgroup α) : NormalAddSubgroup β where
  toSet := U.toSet.image f
  mem_zero := MemZero.image _ U
  mem_neg := MemNeg.image _ U
  mem_add := MemAdd.image _ U
  mem_add_conj := MemAddConj.image _ hf U

def range (f: F) (hf: Function.Surjective f) : NormalAddSubgroup β :=
  (NormalAddSubgroup.image f hf ⊤).copy (Set.range f) (by
    show ∀_, _ ∈ Set.image _ ⊤ ↔ _
    rw [Set.image_univ_eq_range]
    intro x; apply Iff.rfl)

def kernel (f: F) : NormalAddSubgroup α := preimage f ⊥

end NormalAddSubgroup
