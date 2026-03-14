import LeanMath.Algebra.Semigroup.Defs

variable {ι: Type*} {A: ι -> Type*} {α: Type*}

instance [∀i, Mul (A i)] : Mul (∀i, A i) where
  mul a b i := a i * b i

instance [∀i, Add (A i)] : Add (∀i, A i) where
  add a b i := a i + b i

instance [Mul α] : Mul (ι -> α) := inferInstance
instance [Add α] : Add (ι -> α) := inferInstance

structure Apply {ι: Type*} (A: ι -> Type*) (i: ι) where

instance {i: ι} : FunLike (Apply A i) (∀i, A i) (A i) where
  coeFun _ f := f i

instance [∀i, Mul (A i)] : IsMulHom (Apply A i) (∀i, A i) (A i) where
  map_mul _ _ _ := rfl
instance [∀i, Add (A i)] : IsAddHom (Apply A i) (∀i, A i) (A i) where
  map_add _ _ _ := rfl

def Function.apply (i: ι) : Apply A i where

@[simp] def Function.apply_mul [∀i, Mul (A i)] (a b: ∀i, A i) (i: ι) : (a * b) i = a i * b i := rfl
@[simp] def Function.apply_add [∀i, Add (A i)] (a b: ∀i, A i) (i: ι) : (a + b) i = a i + b i := rfl

instance [∀i, Mul (A i)] [∀i, IsSemigroup (A i)] : IsSemigroup (∀i, A i) where
  mul_assoc a b c := by ext i; apply mul_assoc
instance [∀i, Add (A i)] [∀i, IsAddSemigroup (A i)] : IsAddSemigroup (∀i, A i) where
  add_assoc a b c := by ext i; apply add_assoc

instance [∀i, Mul (A i)] [∀i, IsComm (A i)] : IsComm (∀i, A i) where
  mul_comm a b := by ext i; apply mul_comm
instance [∀i, Add (A i)] [∀i, IsAddComm (A i)] : IsAddComm (∀i, A i) where
  add_comm a b := by ext i; apply add_comm

instance [∀i, Mul (A i)] [∀i, IsLeftCancel (A i)] : IsLeftCancel (∀i, A i) where
  of_mul_left h := by ext i; apply of_mul_left (congrFun h _)
instance [∀i, Mul (A i)] [∀i, IsRightCancel (A i)] : IsRightCancel (∀i, A i) where
  of_mul_right h := by ext i; apply of_mul_right (congrFun h _)

instance [∀i, Add (A i)] [∀i, IsLeftAddCancel (A i)] : IsLeftAddCancel (∀i, A i) where
  of_add_left h := by ext i; apply of_add_left (congrFun h _)
instance [∀i, Add (A i)] [∀i, IsRightAddCancel (A i)] : IsRightAddCancel (∀i, A i) where
  of_add_right h := by ext i; apply of_add_right (congrFun h _)

instance [Mul α] [IsSemigroup α] : IsSemigroup (ι -> α) := inferInstance
instance [Add α] [IsAddSemigroup α] : IsAddSemigroup (ι -> α) := inferInstance

instance [Mul α] [IsComm α] : IsComm (ι -> α) := inferInstance
instance [Add α] [IsAddComm α] : IsAddComm (ι -> α) := inferInstance

instance [Mul α] [IsComm α] : IsComm (ι -> α) := inferInstance
instance [Add α] [IsAddComm α] : IsAddComm (ι -> α) := inferInstance

instance [Mul α] [IsLeftCancel α] : IsLeftCancel (ι -> α) := inferInstance
instance [Mul α] [IsRightCancel α] : IsRightCancel (ι -> α) := inferInstance
instance [Add α] [IsLeftAddCancel α] : IsLeftAddCancel (ι -> α) := inferInstance
instance [Add α] [IsRightAddCancel α] : IsRightAddCancel (ι -> α) := inferInstance
