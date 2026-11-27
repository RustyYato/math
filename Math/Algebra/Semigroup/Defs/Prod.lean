module

public import Math.Algebra.Semigroup.Defs.Basic

namespace Math

variable {ι α β: Type*} {γ: ι -> Type*}

section Mul

variable [Mul α] [Mul β] [∀i, Mul (γ i)]

public instance : Mul (α × β) where
  mul a b := (a.fst * b.fst, a.snd * b.snd)

public instance : Mul (∀i, γ i) where
  mul a b i := a i * b i
public instance : Mul (ι -> α) := inferInstance

public instance [IsComm α] [IsComm β] : IsComm (α × β) where
  mul_comm a b := by ext <;> apply mul_comm

public instance [IsSemigroup α] [IsSemigroup β] : IsSemigroup (α × β) where
  mul_assoc a b c := by ext <;> apply mul_assoc

public instance [IsLeftCancel α] [IsLeftCancel β] : IsLeftCancel (α × β) where
  of_mul_left {_ _ _} h := by
    have ⟨_, _⟩ := Prod.mk.inj h
    ext <;> (apply of_mul_left; assumption)

public instance [IsRightCancel α] [IsRightCancel β] : IsRightCancel (α × β) where
  of_mul_right {_ _ _} h := by
    have ⟨_, _⟩ := Prod.mk.inj h
    ext <;> (apply of_mul_right; assumption)

public instance [∀i, IsComm (γ i)] : IsComm (∀i, γ i) where
  mul_comm a b := by ext <;> apply mul_comm

public instance [∀i, IsSemigroup (γ i)] : IsSemigroup (∀i, γ i) where
  mul_assoc a b c := by ext <;> apply mul_assoc

public instance [∀i, IsLeftCancel (γ i)] : IsLeftCancel (∀i, γ i) where
  of_mul_left {_ _ _} h := by ext <;> (apply of_mul_left; apply congrFun h)
public instance [∀i, IsRightCancel (γ i)] : IsRightCancel (∀i, γ i) where
  of_mul_right {_ _ _} h := by ext <;> (apply of_mul_right; apply congrFun h)

public instance [IsComm α] : IsComm (ι -> α) := inferInstance
public instance [IsSemigroup α] : IsSemigroup (ι -> α) := inferInstance

public instance [IsLeftCancel α] : IsLeftCancel (ι -> α) := inferInstance
public instance [IsRightCancel α] : IsRightCancel (ι -> α) := inferInstance

end Mul

section Add

variable [Add α] [Add β] [∀i, Add (γ i)]

public instance : Add (α × β) where
  add a b := (a.fst + b.fst, a.snd + b.snd)

public instance : Add (∀i, γ i) where
  add a b i := a i + b i
public instance : Add (ι -> α) := inferInstance

public instance [IsAddComm α] [IsAddComm β] : IsAddComm (α × β) where
  add_comm a b := by ext <;> apply add_comm

public instance [IsAddSemigroup α] [IsAddSemigroup β] : IsAddSemigroup (α × β) where
  add_assoc a b c := by ext <;> apply add_assoc

public instance [IsLeftAddCancel α] [IsLeftAddCancel β] : IsLeftAddCancel (α × β) where
  of_add_left {_ _ _} h := by
    have ⟨_, _⟩ := Prod.mk.inj h
    ext <;> (apply of_add_left; assumption)

public instance [IsRightAddCancel α] [IsRightAddCancel β] : IsRightAddCancel (α × β) where
  of_add_right {_ _ _} h := by
    have ⟨_, _⟩ := Prod.mk.inj h
    ext <;> (apply of_add_right; assumption)

public instance [∀i, IsAddComm (γ i)] : IsAddComm (∀i, γ i) where
  add_comm a b := by ext <;> apply add_comm

public instance [∀i, IsAddSemigroup (γ i)] : IsAddSemigroup (∀i, γ i) where
  add_assoc a b c := by ext <;> apply add_assoc

public instance [∀i, IsLeftAddCancel (γ i)] : IsLeftAddCancel (∀i, γ i) where
  of_add_left {_ _ _} h := by ext <;> (apply of_add_left; apply congrFun h)
public instance [∀i, IsRightAddCancel (γ i)] : IsRightAddCancel (∀i, γ i) where
  of_add_right {_ _ _} h := by ext <;> (apply of_add_right; apply congrFun h)

public instance [IsAddComm α] : IsAddComm (ι -> α) := inferInstance
public instance [IsAddSemigroup α] : IsAddSemigroup (ι -> α) := inferInstance

public instance [IsLeftAddCancel α] : IsLeftAddCancel (ι -> α) := inferInstance
public instance [IsRightAddCancel α] : IsRightAddCancel (ι -> α) := inferInstance

end Add
