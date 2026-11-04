module

public import Math.Algebra.Monoid.Congruence

namespace Math

public structure GroupQuot (r: α -> α -> Prop) [MonoidOps α] where
  ofQuot :: toQuot : AlgQuot (MulCon.generate r)

namespace GroupQuot

@[local ext]
theorem ext [MonoidOps α] {r: α -> α -> Prop} (a b: GroupQuot r) (h: a.toQuot = b.toQuot) : a = b := by
  cases a; cases b; congr

variable [MonoidOps α] {r: α -> α -> Prop}

def ofQuot' (r: α -> α -> Prop) : AlgQuot (MulCon.generate r) ≃ GroupQuot r where
  toFun := GroupQuot.ofQuot
  invFun := GroupQuot.toQuot
  leftInv _ := rfl
  rightInv _ := rfl

variable [IsMonoid α]

public instance : MonoidOps (GroupQuot r) where
  one := ⟨1⟩
  mul a b := ⟨a.toQuot * b.toQuot⟩
  toPowN := ⟨fun a n => ⟨a.toQuot ^ n⟩⟩

public instance : IsMonoid (GroupQuot r) :=
  OfEquiv.instIsMonoid (ofQuot' r)

@[expose] public def mk (r: α -> α -> Prop) : α →* GroupQuot r where
  toFun := ofQuot ∘ AlgQuot.mk (MulCon.generate r)
  map_one := rfl
  map_mul _ _ := rfl

public theorem sound {a b: α} : r a b -> mk r a = mk r b := by
  intro h; unfold mk
  show ⟨AlgQuot.mk _ _⟩ = ofQuot (AlgQuot.mk _ _)
  congr 1; apply AlgQuot.sound
  apply MulCon.to_generate
  assumption

public theorem exact {a b: α} : mk r a = mk r b -> MulCon.generate r a b := by
  intro h;
  exact AlgQuot.exact (ofQuot.inj h)

@[induction_eliminator]
public theorem ind {motive: GroupQuot r -> Prop} (mk: ∀a, motive (mk r a)) (q: GroupQuot r) : motive q := by
  obtain ⟨q⟩ := q
  induction q with | _ q =>
  apply mk

variable [MonoidOps R] [IsMonoid R]

def preLift [IsMonoid R] (f: α →* R) (hf: ∀a b, r a b -> f a = f b) : GroupQuot r →* R where
  toFun q := q.toQuot.lift f <| by
    intro a b h
    apply MulCon.of_generate (MulCon.eq _) _ _ h
    assumption
  map_one := map_one f
  map_mul a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    apply map_mul (α := α) f a b

theorem preLift_mk (f: α →* R) (hf: ∀a b, r a b -> f a = f b) : preLift f hf (mk r x) = f x := rfl

public def lift : { f: α →* R // ∀a b, r a b -> f a = f b } ≃ GroupQuot r →* R where
  toFun f := preLift f.val f.property
  invFun f := {
    val := f.comp (mk r)
    property := by
      intro a b h; dsimp; congr 1
      apply GroupQuot.sound
      assumption
  }
  leftInv f := by ext a; induction a with | _ a => rfl
  rightInv f := by ext a; rfl

public theorem lift_mk (f: { f: α →* R // ∀a b, r a b -> f a = f b }) : lift f (mk r x) = f.val x := by
  unfold lift
  rfl

end GroupQuot

public structure AddGroupQuot (r: α -> α -> Prop) [AddMonoidOps α] where
  ofQuot :: toQuot : AlgQuot (AddCon.generate r)

namespace AddGroupQuot

@[local ext]
theorem ext [AddMonoidOps α] {r: α -> α -> Prop} (a b: AddGroupQuot r) (h: a.toQuot = b.toQuot) : a = b := by
  cases a; cases b; congr

variable [AddMonoidOps α] {r: α -> α -> Prop}

def ofQuot' (r: α -> α -> Prop) : AlgQuot (AddCon.generate r) ≃ AddGroupQuot r where
  toFun := AddGroupQuot.ofQuot
  invFun := AddGroupQuot.toQuot
  leftInv _ := rfl
  rightInv _ := rfl

variable [IsAddMonoid α]

public instance : AddMonoidOps (AddGroupQuot r) where
  zero := ⟨0⟩
  add a b := ⟨a.toQuot + b.toQuot⟩
  toNSMul := ⟨fun n a => ⟨n • a.toQuot⟩⟩

public instance : IsAddMonoid (AddGroupQuot r) :=
  OfEquiv.instIsAddMonoid (ofQuot' r)

@[expose] public def mk (r: α -> α -> Prop) : α →+ AddGroupQuot r where
  toFun := ofQuot ∘ AlgQuot.mk (AddCon.generate r)
  map_zero := rfl
  map_add _ _ := rfl

public theorem sound {a b: α} : r a b -> mk r a = mk r b := by
  intro h; unfold mk
  show ⟨AlgQuot.mk _ _⟩ = ofQuot (AlgQuot.mk _ _)
  congr 1; apply AlgQuot.sound
  apply AddCon.to_generate
  assumption

public theorem exact {a b: α} : mk r a = mk r b -> AddCon.generate r a b := by
  intro h;
  exact AlgQuot.exact (ofQuot.inj h)

@[induction_eliminator]
public theorem ind {motive: AddGroupQuot r -> Prop} (mk: ∀a, motive (mk r a)) (q: AddGroupQuot r) : motive q := by
  obtain ⟨q⟩ := q
  induction q with | _ q =>
  apply mk

variable [AddMonoidOps R] [IsAddMonoid R]

def preLift [IsAddMonoid R] (f: α →+ R) (hf: ∀a b, r a b -> f a = f b) : AddGroupQuot r →+ R where
  toFun q := q.toQuot.lift f <| by
    intro a b h
    apply AddCon.of_generate (AddCon.eq _) _ _ h
    assumption
  map_zero := map_zero f
  map_add a b := by
    induction a with | _ a =>
    induction b with | _ b =>
    apply map_add (α := α) f a b

theorem preLift_mk (f: α →+ R) (hf: ∀a b, r a b -> f a = f b) : preLift f hf (mk r x) = f x := rfl

public def lift : { f: α →+ R // ∀a b, r a b -> f a = f b } ≃ AddGroupQuot r →+ R where
  toFun f := preLift f.val f.property
  invFun f := {
    val := f.comp (mk r)
    property := by
      intro a b h; dsimp; congr 1
      apply AddGroupQuot.sound
      assumption
  }
  leftInv f := by ext a; induction a with | _ a => rfl
  rightInv f := by ext a; rfl

public theorem lift_mk (f: { f: α →+ R // ∀a b, r a b -> f a = f b }) : lift f (mk r x) = f.val x := by
  unfold lift
  rfl

end AddGroupQuot
