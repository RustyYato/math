module

public import Math.Algebra.Monoid.Defs.Basic

namespace Math

public structure FreeMonoid (α: Type*) where
  ofList :: toList : List α

namespace FreeMonoid

@[expose] public def ι : α ↪ FreeMonoid α where
  toFun x := ⟨[x]⟩
  injective := by intro a b h; cases h; rfl

public instance : One (FreeMonoid α) where
  one := ⟨[]⟩
public instance : Mul (FreeMonoid α) where
  mul a b := ⟨a.toList ++ b.toList⟩

public instance : IsSemigroup (FreeMonoid α) where
  mul_assoc
  | ⟨a⟩, ⟨b⟩, ⟨c⟩ => by
    show ofList (a ++ b ++ c) = ofList (a ++ (b ++ c))
    rw [List.append_assoc]
public instance : IsLawfulOne (FreeMonoid α) where
  one_mul _ := rfl
  mul_one _ := congrArg ofList (List.append_nil _)

public instance : Pow (FreeMonoid α) ℕ :=
  DefaultPowN.instPowNat
public instance : IsLawfulPowN (FreeMonoid α) :=
  DefaultPowN.instIsLawfulPowN
public instance : IsMonoid (FreeMonoid α) where

public theorem list_induction
  {motive: FreeMonoid α -> Prop}
  (one: motive 1)
  (ι_mul: ∀a b, motive b -> motive (ι a * b))
  (m: FreeMonoid α) : motive m := by
  obtain ⟨m⟩ := m
  induction m with
  | nil => apply one
  | cons a as ih => apply ι_mul _ _ ih

@[induction_eliminator]
public theorem induction
  {motive: FreeMonoid α -> Prop}
  (one: motive 1)
  (ι: ∀a, motive (ι a))
  (mul: ∀a b, motive a -> motive b -> motive (a * b))
  (m: FreeMonoid α) : motive m := by
  induction m using list_induction with
  | one => apply one
  | ι_mul a as ih =>
    apply mul; apply ι
    assumption

variable [MonoidOps M] [IsMonoid M]

def preLift (f: α -> M) (val: M) : FreeMonoid α -> M :=
  List.foldl (fun m a => m * f a) val ∘ toList

theorem preLift_eq (f: α -> M) (val: M) (as: FreeMonoid α) :
  preLift f val as = val * preLift f 1 as := by
  induction as using list_induction generalizing val with
  | one => show val = val * 1; rw [mul_one]
  | ι_mul a as ih =>
    show preLift f (val * f a) as = val * preLift f (1 * f a) (as)
    rw [one_mul, ih, ih (f a), mul_assoc]

set_option linter.unusedSectionVars false in
theorem preLift_1 (f: α -> M) : preLift f 1 1 = 1 := rfl
theorem preLift_ι_mul (f: α -> M) (a: α) (as: FreeMonoid α) :
  preLift f 1 (ι a * as) = f a * preLift f 1 as := by
  show preLift f (1 * f a) as = _
  rw [preLift_eq, one_mul]

def preLift' (f: α -> M) : FreeMonoid α →* M where
  toFun := preLift f 1
  map_one := rfl
  map_mul a b := by
    induction a using list_induction with
    | one => rw [one_mul, preLift_1, one_mul]
    | ι_mul  a as ih => rw [mul_assoc, preLift_ι_mul, preLift_ι_mul, ih, mul_assoc]

theorem preLift'_ι (f: α -> M) : preLift' f (ι a) = f a := by
  show preLift _ _ _ = _
  rw [←mul_one (ι a), preLift_ι_mul]
  apply mul_one

public def lift : (α -> M) ≃ (FreeMonoid α →* M) where
  toFun := preLift'
  invFun f := f ∘ ι
  leftInv f := by
    ext a; induction a with
    | one => rw [map_one, map_one]
    | ι a => rw [preLift'_ι]; rfl
    | mul a b iha ihb => rw [map_mul, map_mul]; congr
  rightInv f := by ext a; dsimp; rw [preLift'_ι]

public theorem lift_ι (f: α -> M) (a: α) : lift f (ι a) = f a := preLift'_ι _

public def map (f: α -> β) : FreeMonoid α →* FreeMonoid β :=
  GroupHom.copy (lift (ι ∘ f)) (fun as => ⟨as.toList.map f⟩) <| by
    intro as
    induction as with
    | one | ι => rfl
    | mul a b ha hb =>
      rw [map_mul, ha, hb]
      show ofList _ = _; congr; dsimp
      rw [←List.map_append]
      rfl

@[simp] public theorem map_ι (f: α -> β) (a: α) : FreeMonoid.map f (ι a) = ι (f a) := by rfl

end FreeMonoid

public structure FreeAddMonoid (α: Type*) where
  ofList :: toList : List α

namespace FreeAddMonoid

@[expose] public def ι : α ↪ FreeAddMonoid α where
  toFun x := ⟨[x]⟩
  injective := by intro a b h; cases h; rfl

public instance : Zero (FreeAddMonoid α) where
  zero := ⟨[]⟩
public instance : Add (FreeAddMonoid α) where
  add a b := ⟨a.toList ++ b.toList⟩
public instance : SMul ℕ (FreeAddMonoid α) where
  smul n a := ⟨(FreeMonoid.ofList a.toList ^ n).toList⟩

public def eqv : AddOfMul (FreeMonoid α) ≃+ FreeAddMonoid α where
  toFun a := ⟨a.get.toList⟩
  invFun a :=.mk ⟨a.toList⟩
  leftInv _ := rfl
  rightInv _ := rfl
  map_zero := rfl
  map_add _ _ := rfl

@[simp] public theorem apply_eqv (a: AddOfMul (FreeMonoid α)) : eqv a = ⟨a.get.toList⟩ := by rfl
@[simp] public theorem symm_apply_eqv (a: FreeAddMonoid α) : eqv.symm a = .mk ⟨a.toList⟩ := by rfl

public instance : IsAddMonoid (FreeAddMonoid α) :=
  OfEquiv.instIsAddMonoid eqv.toEquiv

public theorem list_induction
  {motive: FreeAddMonoid α -> Prop}
  (zero: motive 0)
  (ι_add: ∀a b, motive b -> motive (ι a + b))
  (m: FreeAddMonoid α) : motive m := by
  obtain ⟨m⟩ := m
  induction m with
  | nil => apply zero
  | cons a as ih => apply ι_add _ _ ih

@[induction_eliminator]
public theorem induction
  {motive: FreeAddMonoid α -> Prop}
  (zero: motive 0)
  (ι: ∀a, motive (ι a))
  (add: ∀a b, motive a -> motive b -> motive (a + b))
  (m: FreeAddMonoid α) : motive m := by
  induction m using list_induction with
  | zero => apply zero
  | ι_add a as ih =>
    apply add; apply ι
    assumption

variable [AddMonoidOps M] [IsAddMonoid M]

attribute [local irreducible] AddOfMul MulOfAdd

def lift_hom : (FreeAddMonoid α →+ M) ≃ (FreeMonoid α →* MulOfAdd M) where
  toFun f :=
    (GroupHom.of <| MulOfAdd.mk (f.comp eqv.toAddGroupHom)).comp
      (GroupEquiv.mul_of_add_inv_add_of_mul _).symm.toGroupHom
  invFun f :=
    let f := ((AddGroupHom.of (AddOfMul.mk f)).comp eqv.symm.toAddGroupHom)
    (AddGroupEquiv.add_of_mul_inv_mul_of_add _).toAddGroupHom.comp f
  leftInv f := by ext a; simp
  rightInv f := by ext a; simp

def lift_fun : (α -> M) ≃ (α -> MulOfAdd M) where
  toFun f a := MulOfAdd.mk (f a)
  invFun f a := (f a).get
  leftInv _ := rfl
  rightInv _ := rfl

public def lift : (α -> M) ≃ (FreeAddMonoid α →+ M) :=
  lift_fun.trans <| FreeMonoid.lift.trans lift_hom.symm

public theorem lift_ι (f: α -> M) (a: α) : lift f (ι a) = f a := by
  have := fun f' => (lift (α := α) (M := M)).leftInv f'
  simp [lift]
  show lift_hom.invFun (FreeMonoid.lift (MulOfAdd.mk ∘ f)) _ = _
  simp [lift_hom]
  show (FreeMonoid.lift (MulOfAdd.mk ∘ f) (FreeMonoid.ι a)).get = _
  rw [FreeMonoid.lift_ι]
  rfl

public def map (f: α -> β) : FreeAddMonoid α →+ FreeAddMonoid β :=
  AddGroupHom.copy (lift (ι ∘ f)) (fun as => ⟨as.toList.map f⟩) <| by
    intro as
    induction as with
    | zero | ι => rfl
    | add a b ha hb =>
      rw [map_add, ha, hb]
      show ofList _ = _; congr; dsimp
      rw [←List.map_append]
      rfl

@[simp] public theorem map_ι (f: α -> β) (a: α) : FreeAddMonoid.map f (ι a) = ι (f a) := by rfl

end FreeAddMonoid
